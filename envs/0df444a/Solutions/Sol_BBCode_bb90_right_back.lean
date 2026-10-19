-- Prove2me | solution 1 for BBCode.bb90_right_back
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T07:19:14.576205+00:00
-- url     : https://prove2.me/submissions/0a508c23-b23b-49b2-856c-da75d67925a6

import Definitions.Def_BBCode_Setting
open Matrix
namespace BB90Split_right_back
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BB90Cert

def entry {r : ℕ} (v : BitVec r) (i : Fin r) : ZMod 2 :=
  if v.getLsbD i.val then 1 else 0

lemma entry_xor {r : ℕ} (v w : BitVec r) (i : Fin r) :
    entry (v ^^^ w) i = entry v i + entry w i := by
  simp only [entry, BitVec.getLsbD_xor]
  cases v.getLsbD i.val <;> cases w.getLsbD i.val <;> decide

lemma entry_injective {r : ℕ} : Function.Injective (entry (r := r)) := by
  intro v w h
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi := congrFun h (⟨k,hk⟩ : Fin r)
  unfold entry at hi
  cases hv : v.getLsbD k <;> cases hw : w.getLsbD k <;> simp_all

def signature {r n : ℕ} (C : Fin n → BitVec r) (l : List (Fin n)) : BitVec r :=
  l.foldr (fun j a => C j ^^^ a) 0

lemma signature_entry {r n : ℕ} (C : Fin n → BitVec r) (l : List (Fin n))
    (hl : l.Nodup) (i : Fin r) : entry (signature C l) i = ∑ j ∈ l.toFinset, entry (C j) i := by
  induction l with
  | nil => simp [signature, entry]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    simp only [signature, List.foldr_cons, entry_xor]
    rw [show l.foldr (fun j a => C j ^^^ a) 0 = signature C l from rfl, ih hl]
    simp [ha]

def smallLists (n : ℕ) : List (List (Fin n)) :=
  (List.range 5).flatMap fun k => (List.finRange n).sublistsLen k

lemma represent {n : ℕ} (s : Finset (Fin n)) (hs : s.card ≤ 4) :
    ∃ l ∈ smallLists n, l.Nodup ∧ l.toFinset = s := by
  let l := (List.finRange n).filter (fun j => j ∈ s)
  have hl : l.Nodup := (List.nodup_finRange n).filter _
  have he : l.toFinset = s := by ext j; simp [l]
  have hlen : l.length = s.card := by rw [← he, List.toFinset_card_of_nodup hl]
  refine ⟨l, ?_, hl, he⟩
  apply List.mem_flatMap.mpr
  refine ⟨l.length, List.mem_range.mpr (by omega), ?_⟩
  exact List.mem_sublistsLen_self List.filter_sublist

abbrev Item (r : ℕ) := ℕ × BitVec r

def rel {r : ℕ} (a b : Item r) : Prop := a.1 < b.1 ∨ a = b
instance {r : ℕ} : DecidableRel (rel (r := r)) := fun a b =>
  if h : a.1 < b.1 then isTrue (Or.inl h)
  else if e : a = b then isTrue (Or.inr e)
  else isFalse (by intro he; exact he.elim h e)
instance {r : ℕ} : IsTrans (Item r) rel where
  trans a b c hab hbc := by
    rcases hab with hab | rfl <;> rcases hbc with hbc | rfl
    · exact Or.inl (hab.trans hbc)
    · exact Or.inl hab
    · exact Or.inl hbc
    · exact Or.inr rfl

def check {r : ℕ} : List (Item r) → Bool
  | a :: b :: l => if rel a b then check (b :: l) else false
  | _ => true

lemma check_sound {r : ℕ} (l : List (Item r)) (h : check l = true) : l.IsChain rel := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons a l ih =>
    cases l with
    | nil => exact List.IsChain.singleton a
    | cons b l =>
      simp only [check] at h
      split at h
      · exact List.isChain_cons_cons.mpr ⟨by assumption, ih h⟩
      · contradiction

lemma chain_unique {r : ℕ} {l : List (Item r)} (h : l.IsChain rel) :
    ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2 := by
  have hp := List.isChain_iff_pairwise.mp h
  clear h
  induction hp with
  | nil => simp
  | @cons c l hc ht ih =>
    intro a ha b hb he
    by_cases hac : a = c
    · subst a
      by_cases hbc : b = c
      · subst b; rfl
      · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left hbc
        rcases hc _ hb' with hh | hh
        · exact False.elim (by omega)
        · exact congrArg Prod.snd hh
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left hac
      by_cases hbc : b = c
      · subst b
        rcases hc _ ha' with hh | hh
        · exact False.elim (by omega)
        · exact (congrArg Prod.snd hh).symm
      · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left hbc
        exact ih a ha' b hb' he

def item {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (l : List (Fin n)) : Item k := ((signature C l).toNat, signature K l)

def rawItems {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k) : List (Item k) :=
  (List.range 5).flatMap fun j =>
    List.sublistsLenAux j (List.finRange n) (item C K) []

lemma rawItems_eq {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k) :
    rawItems C K = (smallLists n).map (item C K) := by
  simp [rawItems, smallLists, List.map_flatMap, List.sublistsLenAux_eq]

def sortedItems {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k) : List (Item k) :=
  (rawItems C K).mergeSort (fun a b => a.1 ≤ b.1)

lemma small_unique {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (hc : (sortedItems C K).IsChain rel)
    {s t : Finset (Fin n)} (hs : s.card ≤ 4) (ht : t.card ≤ 4)
    (he : (fun i => ∑ j ∈ s, entry (C j) i) = (fun i => ∑ j ∈ t, entry (C j) i)) :
    (fun i => ∑ j ∈ s, entry (K j) i) = (fun i => ∑ j ∈ t, entry (K j) i) := by
  obtain ⟨a,ha,hna,rfl⟩ := represent s hs
  obtain ⟨b,hb,hnb,rfl⟩ := represent t ht
  have hs : signature C a = signature C b := by
    apply entry_injective
    ext i
    simpa [signature_entry C a hna, signature_entry C b hnb] using congrFun he i
  have hm (l : List (Fin n)) (hl : l ∈ smallLists n) : item C K l ∈ sortedItems C K := by
    simp only [sortedItems, rawItems_eq, List.mem_mergeSort]
    exact List.mem_map.mpr ⟨l,hl,rfl⟩
  have h := chain_unique hc _ (hm a ha) _ (hm b hb) (by simp [item,hs])
  change signature K a = signature K b at h
  ext i
  simpa [signature_entry K a hna, signature_entry K b hnb] using congrArg (fun v => entry v i) h

lemma binary_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  have hx : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  exact (hx x).resolve_left h

lemma support_mul {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) (i : Fin r) :
    (H *ᵥ v) i = ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), H i j := by
  change ∑ j, H i j * v j = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : v j = 0
  · simp [h]
  · simp [binary_eq_one h]

lemma kernel_even {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hc : ∀ j, ∑ i, H i j = 1) (v : Fin n → ZMod 2) (hv : H *ᵥ v = 0) :
    2 ∣ weight v := by
  let s := Finset.univ.filter fun j => v j ≠ 0
  apply (ZMod.natCast_eq_zero_iff _ 2).mp
  change (s.card : ZMod 2) = 0
  calc
    (s.card : ZMod 2) = ∑ j ∈ s, (1 : ZMod 2) := by simp
    _ = ∑ j ∈ s, ∑ i, H i j := by simp_rw [hc]
    _ = ∑ i, ∑ j ∈ s, H i j := Finset.sum_comm
    _ = 0 := by
      have he (i) : ∑ j ∈ s, H i j = 0 := by
        rw [← support_mul H v i, hv]; rfl
      simp_rw [he]; simp

lemma split_support {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card ≤ 8) :
    ∃ a b : Finset α, a.card ≤ 4 ∧ b.card ≤ 4 ∧ Disjoint a b ∧ a ∪ b = s := by
  obtain ⟨a,ha,hac⟩ := Finset.exists_subset_card_eq (show min s.card 4 ≤ s.card from min_le_left _ _)
  refine ⟨a,s \ a, ?_, ?_, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset ha⟩
  · omega
  · rw [Finset.card_sdiff_of_subset ha]; omega

lemma small_kernel {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (hc : (sortedItems C K).IsChain rel) (v : Fin n → ZMod 2)
    (hv : (Matrix.of fun i j => entry (C j) i) *ᵥ v = 0) (hw : weight v ≤ 8) :
    (Matrix.of fun i j => entry (K j) i) *ᵥ v = 0 := by
  let s := Finset.univ.filter fun j => v j ≠ 0
  obtain ⟨a,b,ha,hb,hab,hs⟩ := split_support s hw
  have hz (i) : ∑ j ∈ a, entry (C j) i + ∑ j ∈ b, entry (C j) i = 0 := by
    rw [← Finset.sum_union hab, hs]
    change ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), (Matrix.of fun i j => entry (C j) i) i j = 0
    rw [← support_mul _ v i, hv]; rfl
  have he : (fun i => ∑ j ∈ a, entry (C j) i) = (fun i => ∑ j ∈ b, entry (C j) i) := by
    funext i
    exact (eq_neg_of_add_eq_zero_left (hz i)).trans (ZMod.neg_eq_self_mod_two _)
  have hk := small_unique C K hc ha hb he
  funext i
  change ((Matrix.of fun i j => entry (K j) i) *ᵥ v) i = 0
  rw [support_mul]
  change ∑ j ∈ s, entry (K j) i = 0
  rw [← hs, Finset.sum_union hab]
  have hi := congrFun hk i
  rw [hi]
  exact (eq_neg_iff_add_eq_zero.mp (ZMod.neg_eq_self_mod_two _).symm)

lemma transpose_mulVec_mem {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (u : Fin r → ZMod 2) : H.transpose *ᵥ u ∈ rowSpace H := by
  have he : H.transpose *ᵥ u = ∑ i, u i • H i := by
    funext j
    simp [mulVec, dotProduct, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

lemma kernel_mem_row {r k n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (D : Matrix (Fin r) (Fin n) (ZMod 2)) (K : Matrix (Fin k) (Fin n) (ZMod 2))
    (E : Matrix (Fin n) (Fin k) (ZMod 2)) (h : H.transpose * D + E * K = 1) (v : Fin n → ZMod 2) (hv : K *ᵥ v = 0) :
    v ∈ rowSpace H := by
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) (ZMod 2) => M *ᵥ v) h
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at he
  rw [← he]
  exact transpose_mulVec_mem H (D *ᵥ v)

lemma rowspace_reindex {r c a b : Type} [Fintype c] [Fintype b]
    (H : Matrix r c (ZMod 2)) (er : a ≃ r) (ec : b ≃ c) (v : c → ZMod 2) :
    v ∘ ec ∈ rowSpace (H.submatrix er ec) ↔ v ∈ rowSpace H := by
  have forward {r c a b : Type} (H : Matrix r c (ZMod 2)) (er : a ≃ r) (ec : b ≃ c)
      (v : b → ZMod 2) (hv : v ∈ rowSpace (H.submatrix er ec)) :
      v ∘ ec.symm ∈ rowSpace H := by
    change v ∈ Submodule.span (ZMod 2) (Set.range (H.submatrix er ec)) at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i,rfl⟩ := hv
      apply Submodule.subset_span
      exact ⟨er i, by funext j; simp⟩
    | zero => exact Submodule.zero_mem _
    | add v w hv hw ihv ihw => exact Submodule.add_mem _ ihv ihw
    | smul k v hv ih => exact Submodule.smul_mem _ k ih
  constructor
  · intro h
    have hf := forward H er ec (v ∘ ec) h
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hf
  · intro h
    have he : (H.submatrix er ec).submatrix er.symm ec.symm = H := by ext i j; simp
    have hh : v ∈ rowSpace ((H.submatrix er ec).submatrix er.symm ec.symm) := by rwa [he]
    exact forward _ er.symm ec.symm v hh

end BB90Cert

set_option maxHeartbeats 0
open Matrix BBCode BB90Cert
namespace BB90Bits

def unit {n : ℕ} (j : Fin n) : BitVec n := (1 : BitVec n) <<< j.val

lemma unit_entry {n : ℕ} (j i : Fin n) : entry (unit j) i = if i = j then 1 else 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  by_cases h : i = j
  · subst i; simp [unit,entry,hn]
  · have hv : i.val ≠ j.val := by exact fun he => h (Fin.ext he)
    simp [unit,entry,hn,h]
    omega

def combination {r n : ℕ} (rows : Fin r → BitVec n) (c : BitVec r) : BitVec n :=
  (List.finRange r).foldr (fun i v => if c.getLsbD i.val then rows i ^^^ v else v) 0

lemma combination_entry {r n : ℕ} (rows : Fin r → BitVec n) (c : BitVec r) (j : Fin n) :
    entry (combination rows c) j = ∑ i, entry c i * entry (rows i) j := by
  have aux (l : List (Fin r)) :
      entry (l.foldr (fun i v => if c.getLsbD i.val then rows i ^^^ v else v) 0) j =
        (l.map (fun i => entry c i * entry (rows i) j)).sum := by
    induction l with
    | nil => simp [entry]
    | cons a l ih =>
      simp only [List.foldr_cons,List.map_cons,List.sum_cons]
      cases he : c.getLsbD a.val with
      | false =>
        rw [if_neg (by decide),ih]
        have ha : entry c a = 0 := by dsimp only [entry]; rw [he]; rfl
        rw [ha,zero_mul,zero_add]
      | true =>
        rw [if_pos (by decide),entry_xor,ih]
        have ha : entry c a = 1 := by dsimp only [entry]; rw [he]; rfl
        rw [ha,one_mul]
  rw [combination,aux]
  simp [← List.ofFn_eq_map,List.sum_ofFn]

lemma product {a b c : ℕ} (A : Fin a → BitVec b) (B : Fin b → BitVec c)
    (D : Fin a → BitVec c) (h : ∀ i, combination B (A i) = D i) :
    (Matrix.of fun i j => entry (A i) j) * (Matrix.of fun i j => entry (B i) j) =
      (Matrix.of fun i j => entry (D i) j) := by
  apply Matrix.ext
  intro i j
  change ∑ k, entry (A i) k * entry (B k) j = entry (D i) j
  rw [← combination_entry,h]

lemma decomposition {r n : ℕ} (rows : Fin r → BitVec n) (coeff : Fin n → BitVec r)
    (rem : Fin n → BitVec n)
    (h : ∀ j, combination rows (coeff j) ^^^ rem j = unit j) :
    (Matrix.of fun i j => entry (rows i) j).transpose *
        (Matrix.of fun i j => entry (coeff j) i) +
      (Matrix.of fun i j => entry (rem j) i) = 1 := by
  apply Matrix.ext
  intro i j
  have he := congrArg (fun v => entry v i) (h j)
  rw [entry_xor,combination_entry,unit_entry] at he
  change ∑ k, entry (rows k) i * entry (coeff j) k + entry (rem j) i = _
  simpa only [Matrix.one_apply,mul_comm] using he
end BB90Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB90Cert BB90Bits
namespace BB90KernelData
def xmask (j : Fin 90) : BitVec 45 := BitVec.ofNat 45 (#[262150,524293,1048579,2097200,4194344,8388632,16777600,33554752,67109056,134220800,268438016,536872448,1073766400,2147504128,4294979584,8590131200,17180033024,34359836672,68721049600,137440264192,274878693376,549768396800,1099522113536,2199029547008,4398147174400,8796176908288,17592236376064,805306369,671088642,402653188,6442450952,5368709136,3221225504,51539607616,42949673088,25769804032,412316860928,343597384704,206158432256,3298534887424,2748779077632,1649267458048,26388279099392,21990232621056,13194139664384,549772591105,1099545182210,2199090364420,4398180728840,8796361457680,17592722915360,1073741889,2147483778,4294967556,8589935112,17179870224,34359740448,68719480896,137438961792,274877923584,549755847168,1099511694336,2199023388672,4398046777344,8796093554688,17592187109376,2129921,4259842,8519684,17039368,34078736,68157472,136314944,272629888,545259776,1090519552,2181039104,4362078208,8724156416,17448312832,34896625664,69793251328,139586502656,279173005312,558346010624,1116692021248,2233384042496,4466768084992,8933536169984,17867072339968][j])
def xrow (i : Fin 45) : BitVec 90 := BitVec.ofNat 90 (#[73789263279158198278,147578526558316396549,295157053116632793091,590314106233265586224,1180628212466531172392,2361256424933062344728,4722512849866124689792,9445025699732249379136,18890051399464498757824,37780102798928997518336,75560205597857995033088,151120411195715990062592,302240822391431980146688,604481644782863960264704,1208963289565727920500736,2417926579131455841173504,4835853158262911682117632,9671706316525823364005888,19343412633016462357299201,38686825266032924712763394,77373650532065849423691780,154747301064131698858393608,309494602128263397702107152,618989204256526795389534240,38369227708500340113472,76738455417000562786432,153476910834001008132352,306953821668002720907776,613907643336004502291456,1227815286672008065058816,2455630573344021767262208,4911261146688036018331648,9822522293376064520470528,19645044586752174138097664,39290089173504288146653184,78580178347008516163764224,157160356694017393104781312,314320713388034305173225472,628641426776068129310113792,19342814266794054311215104,38685628533584260331732992,77371257067164672372768768,154742514134352434489720832,309485028268674082653863936,618970056537317378982150144][i])
def xH : Matrix (Fin 45) (Fin 90) (ZMod 2) := fun i j => entry (xmask j) i
lemma xrow_bits : ∀ i j, (xrow i).getLsbD j.val = (xmask j).getLsbD i.val := by decide +kernel
lemma xrow_entry (i : Fin 45) (j : Fin 90) : entry (xrow i) j = xH i j := by
  change entry (xrow i) j = entry (xmask j) i
  unfold entry; rw [xrow_bits]
def zmask (j : Fin 90) : BitVec 45 := BitVec.ofNat 45 (#[2097217,4194434,8388868,16777736,33555472,67110944,134221888,268443776,536887552,1073775104,2147550208,4295100416,8590200832,17180401664,34360803328,68721606656,137443213312,274886426624,549772853248,1099545706496,2199091412992,4398182825984,8796365651968,17592731303936,1090519041,2181038082,4362076164,8724152328,17448304656,34896609312,69793218624,139586437248,279172874496,558345748992,1116691497984,2233382995968,4466765991936,8933531983872,17867063967744,549755846657,1099511693314,2199023386628,4398046773256,8796093546512,17592187093024,134217734,268435461,536870915,1073741872,2147483688,4294967320,8589934976,17179869504,34359738560,68719479808,137438956032,274877908480,549755838464,1099511648256,2199023267840,4398046707712,8796093186048,17592186142720,1572865,1310722,786436,12582920,10485776,6291488,100663360,83886208,50331904,805306880,671089664,402655232,6442455040,5368717312,3221241856,51539640320,42949738496,25769934848,412317122560,343597907968,206159478784,3298536980480,2748783263744,1649275830272,26388295843840,21990266109952,13194206642176][j])
def zrow (i : Fin 45) : BitVec 90 := BitVec.ofNat 90 (#[9223583692859899905,18446921095115177986,36893595899625734148,73788669542879199240,147575368760921423888,295148767197005873184,590309321158661505089,1180602879718627213442,2361189996838558630148,4722474569269292040712,9444823037749017707536,18889519974708469041184,37779796554154336325696,75558584301992141660288,151116159797667752329472,302238372433234690605568,604468674415937133282304,1208929278381342018635776,2417906979465877524844544,4835749395327497066258432,9671434227050736149086208,19343255835691835826667521,38685995162549607785889794,77371473816265151704334340,154746046685534686613340168,309487961300396862287118352,618971790530121213634674720,28334198932402379685952,23611832484717242876032,14167099589346969256192,226673591459219037487616,188894659877737943008256,113336796714775754049536,1813388731673752299900928,1511157279021903544066048,906694373718206032396288,14507109853390018399207424,12089258232175228352528384,7253554989745648259170304,116056878827120147193659392,96714065857401826820227072,58028439917965186073362432,928455030616961177549275136,773712526859214614561816576,464227519343721488586899456][i])
def zH : Matrix (Fin 45) (Fin 90) (ZMod 2) := fun i j => entry (zmask j) i
lemma zrow_bits : ∀ i j, (zrow i).getLsbD j.val = (zmask j).getLsbD i.val := by decide +kernel
lemma zrow_entry (i : Fin 45) (j : Fin 90) : entry (zrow i) j = zH i j := by
  change entry (zrow i) j = entry (zmask j) i
  unfold entry; rw [zrow_bits]
def xcoef (j : Fin 90) : BitVec 45 := BitVec.ofNat 45 (#[77309448776,5112103810264,5266722707816,558346010632,4632546158147,4789585103429,4466768085056,4492993857091,4510480501317,627082039369,19634128000,39268256000,618492105281,4959939170520,4962393428328,627082006601,19634062464,39268124928,618492367425,4959938646232,4962392379752,549774721537,5097373937752,5237262962792,77309448777,774304511643,928923409197,558346010624,776724559387,933763504685,4406638580296,757431284251,895176954413,68736553537,4612980319939,4750453427013,4947821232641,639012976283,658340338477,0,0,0,0,0,0,4475507212865,0,0,4957484912712,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0][j])
def xrem (j : Fin 90) : BitVec 90 := BitVec.ofNat 90 (#[16665903326610973523968000,1230888146894653313159004160,1225985004914507545262948352,120288248326920506355744768,1127592335238946096110632960,1171717961342013471287410688,962305986615364050845958144,824488960856818890146054144,548854909339728568746246144,287464115588279131353120768,355348463729991691379146752,708279076831812240753557504,285655375542505105734500352,876872669807734649406881792,532999371121806827623284736,287161877215845896662548480,354743995055575754245931008,707070147553430898735054848,288073282521970983259078656,872036920412424744527200256,523327936894791275847352320,290453151418931749748473856,927573545221037207731568640,617475644958016789794521088,16665912550193566855462912,142565123463956707904847872,147316836699677106743803904,120288174538259759703785472,103060972531751192801312768,68606568518734058996367360,949957079925865173477228544,406400366640714139492679680,677132456764775810780364800,172016403694850844655616000,775322854555022934887366656,465299496976826124134776832,1218908182035892858576175104,153861018361840322798944256,153248125614330760466006016,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,1102275377445820033220476928,70368744177664,140737488355328,1220981956555127381433516032,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808,18446744073709551616,36893488147419103232,73786976294838206464,147573952589676412928,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112][j])
def xD : Matrix (Fin 45) (Fin 90) (ZMod 2) := fun i j => entry (xcoef j) i
def xK : Matrix (Fin 90) (Fin 90) (ZMod 2) := fun i j => entry (xrem j) i
lemma xdecomp_bits : ∀ j, combination zrow (xcoef j) ^^^ xrem j = unit j := by decide +kernel
lemma xdecomp : zH.transpose * xD + xK = 1 := by
  have h := decomposition zrow xcoef xrem xdecomp_bits
  have he : (Matrix.of fun i j => entry (zrow i) j) = zH := by
    apply Matrix.ext; intro i j; exact zrow_entry i j
  rw [he] at h
  exact h
def xrows (i : Fin 41) : Fin 45 := ⟨#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,42][i], by fin_cases i <;> decide⟩
def xpiv (i : Fin 41) : Fin 90 := ⟨#[1,0,27,4,3,30,7,6,33,10,9,36,13,12,39,16,15,42,2,18,19,5,21,22,8,24,25,11,29,28,14,32,31,17,35,34,20,45,46,23,26][i], by fin_cases i <;> decide⟩
def xLmask (i : Fin 45) : BitVec 41 := BitVec.ofNat 41 (#[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,759545214491,899404814893,1099511627776,1331893733059,1486815136581][i])
def xL : Matrix (Fin 45) (Fin 41) (ZMod 2) := fun i j => entry (xLmask i) j
def xR : Matrix (Fin 41) (Fin 90) (ZMod 2) := xH.submatrix xrows id
lemma xfactor_bits : ∀ i, combination (fun j => xrow (xrows j)) (xLmask i) = xrow i := by decide +kernel
lemma xfactor : xH = xL * xR := by
  have h := product xLmask (fun j => xrow (xrows j)) xrow xfactor_bits
  have he : (Matrix.of fun i j => entry (xrow i) j) = xH := by
    apply Matrix.ext; intro i j; exact xrow_entry i j
  have hr : (Matrix.of fun i j => entry (xrow (xrows i)) j) = xR := by
    apply Matrix.ext; intro i j; exact xrow_entry (xrows i) j
  rw [he,hr] at h
  exact h.symm
def xMmask (i : Fin 41) : BitVec 41 := BitVec.ofNat 41 (#[137439215621,275415040002,268435459,2097192,4297064464,2147483672,16777536,34376515712,17179869376,134220288,134218752,1536,1073762304,1073750016,12288,8590098432,8590000128,98304,68720525314,68720001025,1835008,549764202512,549760008200,14680064,1237017690240,1374423089216,117440512,805307392,268435972,671088644,6442459136,2147487776,5368709152,51539673088,17179902208,42949673216,524288,1050624,68719478784,137443147776,33554432][i])
def xImask (i : Fin 41) : BitVec 41 := BitVec.ofNat 41 (#[343597911552,412317122560,206830307844,5383397416,6457155632,6442475576,249629050691,258219116419,51539804608,939525120,939527168,3584,7516200960,7516217344,28672,60129607680,60129738752,229376,206159482368,68719476736,137438957056,3235921944,894025599493,897253132829,232449246915,1099511627776,1331893765827,939526144,206159220228,206964523524,7516209152,3221241912,5368717368,60129673216,25769935296,42949738944,274877910528,344269785605,413123742726,899404802605,1486815038277][i])
def xInv : Matrix (Fin 41) (Fin 41) (ZMod 2) := fun i j => entry (xImask i) j
lemma xminor_bits : ∀ i, combination xImask (xMmask i) = unit i := by decide +kernel
lemma xM_bits : ∀ i j, (xMmask i).getLsbD j.val = (xrow (xrows i)).getLsbD (xpiv j).val := by decide +kernel
lemma xminor : (xH.submatrix xrows xpiv) * xInv = 1 := by
  have h := product xMmask xImask unit xminor_bits
  have hm : (Matrix.of fun i j => entry (xMmask i) j) = xH.submatrix xrows xpiv := by
    apply Matrix.ext
    intro i j
    change entry (xMmask i) j = xH (xrows i) (xpiv j)
    rw [← xrow_entry]
    unfold entry
    rw [xM_bits]
  have hu : (Matrix.of fun i j => entry (unit i) j) = (1 : Matrix (Fin 41) (Fin 41) (ZMod 2)) := by
    apply Matrix.ext; intro i j
    change entry (unit i) j = if i = j then 1 else 0
    rw [unit_entry]
    simp only [eq_comm]
  rw [hm,hu] at h
  exact h
lemma xrank : xH.rank = 41 := by
  apply Nat.le_antisymm
  · rw [xfactor]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)
  · have h := Matrix.rank_mul_le_left (xH.submatrix xrows xpiv) xInv
    rw [xminor,Matrix.rank_one,Fintype.card_fin] at h
    exact h.trans (Matrix.rank_submatrix_le _ _ _)
lemma xcolParity : ∀ j, ∑ i, xH i j = 1 := by decide +kernel
def decode (key : ℕ) : ℕ := (if key < 34896625664 then (if key < 671088642 then (if key < 33554752 then (if key < 4194344 then (if key < 1048579 then (if key < 524293 then 0 else 1) else (if key < 2097200 then 2 else (if key < 2129921 then 3 else 66))) else (if key < 8519684 then (if key < 4259842 then 4 else (if key < 8388632 then 67 else 5)) else (if key < 16777600 then 68 else (if key < 17039368 then 6 else 69)))) else (if key < 136314944 then (if key < 67109056 then (if key < 34078736 then 7 else 70) else (if key < 68157472 then 8 else (if key < 134220800 then 71 else 9))) else (if key < 402653188 then (if key < 268438016 then 72 else (if key < 272629888 then 10 else 73)) else (if key < 536872448 then 29 else (if key < 545259776 then 11 else 74))))) else (if key < 4362078208 then (if key < 2147483778 then (if key < 1073741889 then (if key < 805306369 then 28 else 27) else (if key < 1073766400 then 51 else (if key < 1090519552 then 12 else 75))) else (if key < 3221225504 then (if key < 2147504128 then 52 else (if key < 2181039104 then 13 else 76)) else (if key < 4294967556 then 32 else (if key < 4294979584 then 53 else 14)))) else (if key < 17179870224 then (if key < 8589935112 then (if key < 5368709136 then 77 else (if key < 6442450952 then 31 else 30)) else (if key < 8590131200 then 54 else (if key < 8724156416 then 15 else 78))) else (if key < 25769804032 then (if key < 17180033024 then 55 else (if key < 17448312832 then 16 else 79)) else (if key < 34359740448 then 35 else (if key < 34359836672 then 56 else 17)))))) else (if key < 1116692021248 then (if key < 274878693376 then (if key < 69793251328 then (if key < 51539607616 then (if key < 42949673088 then 80 else 34) else (if key < 68719480896 then 33 else (if key < 68721049600 then 57 else 18))) else (if key < 139586502656 then (if key < 137438961792 then 81 else (if key < 137440264192 then 58 else 19)) else (if key < 206158432256 then 82 else (if key < 274877923584 then 38 else 59)))) else (if key < 549768396800 then (if key < 343597384704 then (if key < 279173005312 then 20 else 83) else (if key < 412316860928 then 37 else (if key < 549755847168 then 36 else 60))) else (if key < 1099511694336 then (if key < 549772591105 then 21 else (if key < 558346010624 then 45 else 84)) else (if key < 1099522113536 then 61 else (if key < 1099545182210 then 22 else 46))))) else (if key < 4466768084992 then (if key < 2233384042496 then (if key < 2199023388672 then (if key < 1649267458048 then 85 else 41) else (if key < 2199029547008 then 62 else (if key < 2199090364420 then 23 else 47))) else (if key < 4398046777344 then (if key < 2748779077632 then 86 else (if key < 3298534887424 then 40 else 39)) else (if key < 4398147174400 then 63 else (if key < 4398180728840 then 24 else 48)))) else (if key < 17592187109376 then (if key < 8796361457680 then (if key < 8796093554688 then 87 else (if key < 8796176908288 then 64 else 25)) else (if key < 8933536169984 then 49 else (if key < 13194139664384 then 88 else 44))) else (if key < 17867072339968 then (if key < 17592236376064 then 65 else (if key < 17592722915360 then 26 else 50)) else (if key < 21990232621056 then 89 else (if key < 26388279099392 then 43 else 42)))))))
lemma decode_left : ∀ j, decode (xmask j).toNat = j.val := by decide +kernel
lemma xinjective : Function.Injective xmask := by
  intro i j h
  apply Fin.ext
  rw [← decode_left i,← decode_left j,h]
lemma xnonzero : ∀ j, xmask j ≠ 0 := by decide +kernel
def xneighbors (i : Fin 45) : List (Fin 90) := #[[1,2,27,45,51,66],[0,2,28,46,52,67],[0,1,29,47,53,68],[4,5,30,48,54,69],[3,5,31,49,55,70],[3,4,32,50,56,71],[7,8,33,51,57,72],[6,8,34,52,58,73],[6,7,35,53,59,74],[10,11,36,54,60,75],[9,11,37,55,61,76],[9,10,38,56,62,77],[13,14,39,57,63,78],[12,14,40,58,64,79],[12,13,41,59,65,80],[16,17,42,60,66,81],[15,17,43,61,67,82],[15,16,44,62,68,83],[0,19,20,63,69,84],[1,18,20,64,70,85],[2,18,19,65,71,86],[3,22,23,66,72,87],[4,21,23,67,73,88],[5,21,22,68,74,89],[6,25,26,45,69,75],[7,24,26,46,70,76],[8,24,25,47,71,77],[9,28,29,48,72,78],[10,27,29,49,73,79],[11,27,28,50,74,80],[12,31,32,51,75,81],[13,30,32,52,76,82],[14,30,31,53,77,83],[15,34,35,54,78,84],[16,33,35,55,79,85],[17,33,34,56,80,86],[18,37,38,57,81,87],[19,36,38,58,82,88],[20,36,37,59,83,89],[21,40,41,45,60,84],[22,39,41,46,61,85],[23,39,40,47,62,86],[24,43,44,48,63,87],[25,42,44,49,64,88],[26,42,43,50,65,89]][i]
def xnbr (i : Fin 45) (t : Fin 6) : Fin 90 := (xneighbors i).getD t.val 0
end BB90KernelData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB90Cert
namespace BB90Search

def pick {r : ℕ} [NeZero r] (s : BitVec r) : Fin r :=
  ((List.finRange r).find? fun i => s.getLsbD i.val).getD 0

lemma pick_spec {r : ℕ} [NeZero r] (s : BitVec r) (hs : s ≠ 0) :
    s.getLsbD (pick s).val = true := by
  unfold pick
  cases hf : (List.finRange r).find? (fun i => s.getLsbD i.val) with
  | none =>
    have he : s = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have h := List.find?_eq_none.mp hf ⟨i,hi⟩ (by simp)
      simpa using h
    exact False.elim (hs he)
  | some i =>
    simpa using List.find?_some hf

def ones {r : ℕ} (s : BitVec r) : ℕ :=
  ((List.finRange r).map fun i => (s.getLsbD i.val).toNat).sum

lemma ones_eq {r : ℕ} (s : BitVec r) : ones s = ∑ i : Fin r, (s.getLsbD i.val).toNat := by
  simp [ones, ← List.sum_ofFn, List.ofFn_eq_map]

lemma ones_xor_le {r : ℕ} (s t : BitVec r) : ones (s ^^^ t) ≤ ones s + ones t := by
  rw [ones_eq,ones_eq,ones_eq,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases s.getLsbD i.val <;> cases t.getLsbD i.val <;> decide

lemma ones_sig_le {r n : ℕ} (C : Fin n → BitVec r) (hC : ∀ j, ones (C j) ≤ 3)
    (l : List (Fin n)) : ones (signature C l) ≤ 3*l.length := by
  induction l with
  | nil => simp [signature,ones]
  | cons a l ih =>
    have h := ones_xor_le (C a) (signature C l)
    change ones (signature C (a::l)) ≤ _ at h
    have ha := hC a
    simp only [List.length_cons]
    omega

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) : ℕ → List (Fin n) → BitVec r → Bool
  | fuel, used, sy =>
    if 3 * fuel < ones sy then true
    else if sy = 0 then decide (fuel = 2) && decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => (nbr (pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr fuel (j :: used) (C j ^^^ sy)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) :
    check C K nbr fuel used sy =
      if 3 * fuel < ones sy then true
      else if sy = 0 then decide (fuel = 2) && decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => (nbr (pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr f (j :: used) (C j ^^^ sy) := by
  cases fuel <;> rfl
end BB90Search

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Matrix BBCode BB90Cert BB90Bits BB90Search
namespace BB90KernelData
def polyA : Poly 15 3 := {(9,0),(0,1),(0,2)}
def polyB : Poly 15 3 := {(0,0),(2,0),(7,0)}
def er : Fin 45 ≃ Grp 15 3 where
  toFun i := ((i.val / 3 : ℕ), (i.val % 3 : ℕ))
  invFun g := ⟨g.1.val * 3 + g.2.val, by
    have h1 := ZMod.val_lt g.1
    have h2 := ZMod.val_lt g.2
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eqb : Fin 90 ≃ Qubit 15 3 where
  toFun i := if h : i.val < 45 then Sum.inl (er ⟨i.val,h⟩)
    else Sum.inr (er ⟨i.val-45,by omega⟩)
  invFun q := match q with
    | Sum.inl g => ⟨(er.symm g).val, by have h := (er.symm g).isLt; omega⟩
    | Sum.inr g => ⟨45 + (er.symm g).val, by have h := (er.symm g).isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma xtable_0 : ∀ j, (HX polyA polyB) (er 0) (eqb j) = xH 0 j := by decide +kernel
lemma xtable_1 : ∀ j, (HX polyA polyB) (er 1) (eqb j) = xH 1 j := by decide +kernel
lemma xtable_2 : ∀ j, (HX polyA polyB) (er 2) (eqb j) = xH 2 j := by decide +kernel
lemma xtable_3 : ∀ j, (HX polyA polyB) (er 3) (eqb j) = xH 3 j := by decide +kernel
lemma xtable_4 : ∀ j, (HX polyA polyB) (er 4) (eqb j) = xH 4 j := by decide +kernel
lemma xtable_5 : ∀ j, (HX polyA polyB) (er 5) (eqb j) = xH 5 j := by decide +kernel
lemma xtable_6 : ∀ j, (HX polyA polyB) (er 6) (eqb j) = xH 6 j := by decide +kernel
lemma xtable_7 : ∀ j, (HX polyA polyB) (er 7) (eqb j) = xH 7 j := by decide +kernel
lemma xtable_8 : ∀ j, (HX polyA polyB) (er 8) (eqb j) = xH 8 j := by decide +kernel
lemma xtable_9 : ∀ j, (HX polyA polyB) (er 9) (eqb j) = xH 9 j := by decide +kernel
lemma xtable_10 : ∀ j, (HX polyA polyB) (er 10) (eqb j) = xH 10 j := by decide +kernel
lemma xtable_11 : ∀ j, (HX polyA polyB) (er 11) (eqb j) = xH 11 j := by decide +kernel
lemma xtable_12 : ∀ j, (HX polyA polyB) (er 12) (eqb j) = xH 12 j := by decide +kernel
lemma xtable_13 : ∀ j, (HX polyA polyB) (er 13) (eqb j) = xH 13 j := by decide +kernel
lemma xtable_14 : ∀ j, (HX polyA polyB) (er 14) (eqb j) = xH 14 j := by decide +kernel
lemma xtable_15 : ∀ j, (HX polyA polyB) (er 15) (eqb j) = xH 15 j := by decide +kernel
lemma xtable_16 : ∀ j, (HX polyA polyB) (er 16) (eqb j) = xH 16 j := by decide +kernel
lemma xtable_17 : ∀ j, (HX polyA polyB) (er 17) (eqb j) = xH 17 j := by decide +kernel
lemma xtable_18 : ∀ j, (HX polyA polyB) (er 18) (eqb j) = xH 18 j := by decide +kernel
lemma xtable_19 : ∀ j, (HX polyA polyB) (er 19) (eqb j) = xH 19 j := by decide +kernel
lemma xtable_20 : ∀ j, (HX polyA polyB) (er 20) (eqb j) = xH 20 j := by decide +kernel
lemma xtable_21 : ∀ j, (HX polyA polyB) (er 21) (eqb j) = xH 21 j := by decide +kernel
lemma xtable_22 : ∀ j, (HX polyA polyB) (er 22) (eqb j) = xH 22 j := by decide +kernel
lemma xtable_23 : ∀ j, (HX polyA polyB) (er 23) (eqb j) = xH 23 j := by decide +kernel
lemma xtable_24 : ∀ j, (HX polyA polyB) (er 24) (eqb j) = xH 24 j := by decide +kernel
lemma xtable_25 : ∀ j, (HX polyA polyB) (er 25) (eqb j) = xH 25 j := by decide +kernel
lemma xtable_26 : ∀ j, (HX polyA polyB) (er 26) (eqb j) = xH 26 j := by decide +kernel
lemma xtable_27 : ∀ j, (HX polyA polyB) (er 27) (eqb j) = xH 27 j := by decide +kernel
lemma xtable_28 : ∀ j, (HX polyA polyB) (er 28) (eqb j) = xH 28 j := by decide +kernel
lemma xtable_29 : ∀ j, (HX polyA polyB) (er 29) (eqb j) = xH 29 j := by decide +kernel
lemma xtable_30 : ∀ j, (HX polyA polyB) (er 30) (eqb j) = xH 30 j := by decide +kernel
lemma xtable_31 : ∀ j, (HX polyA polyB) (er 31) (eqb j) = xH 31 j := by decide +kernel
lemma xtable_32 : ∀ j, (HX polyA polyB) (er 32) (eqb j) = xH 32 j := by decide +kernel
lemma xtable_33 : ∀ j, (HX polyA polyB) (er 33) (eqb j) = xH 33 j := by decide +kernel
lemma xtable_34 : ∀ j, (HX polyA polyB) (er 34) (eqb j) = xH 34 j := by decide +kernel
lemma xtable_35 : ∀ j, (HX polyA polyB) (er 35) (eqb j) = xH 35 j := by decide +kernel
lemma xtable_36 : ∀ j, (HX polyA polyB) (er 36) (eqb j) = xH 36 j := by decide +kernel
lemma xtable_37 : ∀ j, (HX polyA polyB) (er 37) (eqb j) = xH 37 j := by decide +kernel
lemma xtable_38 : ∀ j, (HX polyA polyB) (er 38) (eqb j) = xH 38 j := by decide +kernel
lemma xtable_39 : ∀ j, (HX polyA polyB) (er 39) (eqb j) = xH 39 j := by decide +kernel
lemma xtable_40 : ∀ j, (HX polyA polyB) (er 40) (eqb j) = xH 40 j := by decide +kernel
lemma xtable_41 : ∀ j, (HX polyA polyB) (er 41) (eqb j) = xH 41 j := by decide +kernel
lemma xtable_42 : ∀ j, (HX polyA polyB) (er 42) (eqb j) = xH 42 j := by decide +kernel
lemma xtable_43 : ∀ j, (HX polyA polyB) (er 43) (eqb j) = xH 43 j := by decide +kernel
lemma xtable_44 : ∀ j, (HX polyA polyB) (er 44) (eqb j) = xH 44 j := by decide +kernel
lemma xtable : (HX polyA polyB).submatrix er eqb = xH := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact xtable_0 j
  · exact xtable_1 j
  · exact xtable_2 j
  · exact xtable_3 j
  · exact xtable_4 j
  · exact xtable_5 j
  · exact xtable_6 j
  · exact xtable_7 j
  · exact xtable_8 j
  · exact xtable_9 j
  · exact xtable_10 j
  · exact xtable_11 j
  · exact xtable_12 j
  · exact xtable_13 j
  · exact xtable_14 j
  · exact xtable_15 j
  · exact xtable_16 j
  · exact xtable_17 j
  · exact xtable_18 j
  · exact xtable_19 j
  · exact xtable_20 j
  · exact xtable_21 j
  · exact xtable_22 j
  · exact xtable_23 j
  · exact xtable_24 j
  · exact xtable_25 j
  · exact xtable_26 j
  · exact xtable_27 j
  · exact xtable_28 j
  · exact xtable_29 j
  · exact xtable_30 j
  · exact xtable_31 j
  · exact xtable_32 j
  · exact xtable_33 j
  · exact xtable_34 j
  · exact xtable_35 j
  · exact xtable_36 j
  · exact xtable_37 j
  · exact xtable_38 j
  · exact xtable_39 j
  · exact xtable_40 j
  · exact xtable_41 j
  · exact xtable_42 j
  · exact xtable_43 j
  · exact xtable_44 j
lemma ztable_0 : ∀ j, (HZ polyA polyB) (er 0) (eqb j) = zH 0 j := by decide +kernel
lemma ztable_1 : ∀ j, (HZ polyA polyB) (er 1) (eqb j) = zH 1 j := by decide +kernel
lemma ztable_2 : ∀ j, (HZ polyA polyB) (er 2) (eqb j) = zH 2 j := by decide +kernel
lemma ztable_3 : ∀ j, (HZ polyA polyB) (er 3) (eqb j) = zH 3 j := by decide +kernel
lemma ztable_4 : ∀ j, (HZ polyA polyB) (er 4) (eqb j) = zH 4 j := by decide +kernel
lemma ztable_5 : ∀ j, (HZ polyA polyB) (er 5) (eqb j) = zH 5 j := by decide +kernel
lemma ztable_6 : ∀ j, (HZ polyA polyB) (er 6) (eqb j) = zH 6 j := by decide +kernel
lemma ztable_7 : ∀ j, (HZ polyA polyB) (er 7) (eqb j) = zH 7 j := by decide +kernel
lemma ztable_8 : ∀ j, (HZ polyA polyB) (er 8) (eqb j) = zH 8 j := by decide +kernel
lemma ztable_9 : ∀ j, (HZ polyA polyB) (er 9) (eqb j) = zH 9 j := by decide +kernel
lemma ztable_10 : ∀ j, (HZ polyA polyB) (er 10) (eqb j) = zH 10 j := by decide +kernel
lemma ztable_11 : ∀ j, (HZ polyA polyB) (er 11) (eqb j) = zH 11 j := by decide +kernel
lemma ztable_12 : ∀ j, (HZ polyA polyB) (er 12) (eqb j) = zH 12 j := by decide +kernel
lemma ztable_13 : ∀ j, (HZ polyA polyB) (er 13) (eqb j) = zH 13 j := by decide +kernel
lemma ztable_14 : ∀ j, (HZ polyA polyB) (er 14) (eqb j) = zH 14 j := by decide +kernel
lemma ztable_15 : ∀ j, (HZ polyA polyB) (er 15) (eqb j) = zH 15 j := by decide +kernel
lemma ztable_16 : ∀ j, (HZ polyA polyB) (er 16) (eqb j) = zH 16 j := by decide +kernel
lemma ztable_17 : ∀ j, (HZ polyA polyB) (er 17) (eqb j) = zH 17 j := by decide +kernel
lemma ztable_18 : ∀ j, (HZ polyA polyB) (er 18) (eqb j) = zH 18 j := by decide +kernel
lemma ztable_19 : ∀ j, (HZ polyA polyB) (er 19) (eqb j) = zH 19 j := by decide +kernel
lemma ztable_20 : ∀ j, (HZ polyA polyB) (er 20) (eqb j) = zH 20 j := by decide +kernel
lemma ztable_21 : ∀ j, (HZ polyA polyB) (er 21) (eqb j) = zH 21 j := by decide +kernel
lemma ztable_22 : ∀ j, (HZ polyA polyB) (er 22) (eqb j) = zH 22 j := by decide +kernel
lemma ztable_23 : ∀ j, (HZ polyA polyB) (er 23) (eqb j) = zH 23 j := by decide +kernel
lemma ztable_24 : ∀ j, (HZ polyA polyB) (er 24) (eqb j) = zH 24 j := by decide +kernel
lemma ztable_25 : ∀ j, (HZ polyA polyB) (er 25) (eqb j) = zH 25 j := by decide +kernel
lemma ztable_26 : ∀ j, (HZ polyA polyB) (er 26) (eqb j) = zH 26 j := by decide +kernel
lemma ztable_27 : ∀ j, (HZ polyA polyB) (er 27) (eqb j) = zH 27 j := by decide +kernel
lemma ztable_28 : ∀ j, (HZ polyA polyB) (er 28) (eqb j) = zH 28 j := by decide +kernel
lemma ztable_29 : ∀ j, (HZ polyA polyB) (er 29) (eqb j) = zH 29 j := by decide +kernel
lemma ztable_30 : ∀ j, (HZ polyA polyB) (er 30) (eqb j) = zH 30 j := by decide +kernel
lemma ztable_31 : ∀ j, (HZ polyA polyB) (er 31) (eqb j) = zH 31 j := by decide +kernel
lemma ztable_32 : ∀ j, (HZ polyA polyB) (er 32) (eqb j) = zH 32 j := by decide +kernel
lemma ztable_33 : ∀ j, (HZ polyA polyB) (er 33) (eqb j) = zH 33 j := by decide +kernel
lemma ztable_34 : ∀ j, (HZ polyA polyB) (er 34) (eqb j) = zH 34 j := by decide +kernel
lemma ztable_35 : ∀ j, (HZ polyA polyB) (er 35) (eqb j) = zH 35 j := by decide +kernel
lemma ztable_36 : ∀ j, (HZ polyA polyB) (er 36) (eqb j) = zH 36 j := by decide +kernel
lemma ztable_37 : ∀ j, (HZ polyA polyB) (er 37) (eqb j) = zH 37 j := by decide +kernel
lemma ztable_38 : ∀ j, (HZ polyA polyB) (er 38) (eqb j) = zH 38 j := by decide +kernel
lemma ztable_39 : ∀ j, (HZ polyA polyB) (er 39) (eqb j) = zH 39 j := by decide +kernel
lemma ztable_40 : ∀ j, (HZ polyA polyB) (er 40) (eqb j) = zH 40 j := by decide +kernel
lemma ztable_41 : ∀ j, (HZ polyA polyB) (er 41) (eqb j) = zH 41 j := by decide +kernel
lemma ztable_42 : ∀ j, (HZ polyA polyB) (er 42) (eqb j) = zH 42 j := by decide +kernel
lemma ztable_43 : ∀ j, (HZ polyA polyB) (er 43) (eqb j) = zH 43 j := by decide +kernel
lemma ztable_44 : ∀ j, (HZ polyA polyB) (er 44) (eqb j) = zH 44 j := by decide +kernel
lemma ztable : (HZ polyA polyB).submatrix er eqb = zH := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact ztable_0 j
  · exact ztable_1 j
  · exact ztable_2 j
  · exact ztable_3 j
  · exact ztable_4 j
  · exact ztable_5 j
  · exact ztable_6 j
  · exact ztable_7 j
  · exact ztable_8 j
  · exact ztable_9 j
  · exact ztable_10 j
  · exact ztable_11 j
  · exact ztable_12 j
  · exact ztable_13 j
  · exact ztable_14 j
  · exact ztable_15 j
  · exact ztable_16 j
  · exact ztable_17 j
  · exact ztable_18 j
  · exact ztable_19 j
  · exact ztable_20 j
  · exact ztable_21 j
  · exact ztable_22 j
  · exact ztable_23 j
  · exact ztable_24 j
  · exact ztable_25 j
  · exact ztable_26 j
  · exact ztable_27 j
  · exact ztable_28 j
  · exact ztable_29 j
  · exact ztable_30 j
  · exact ztable_31 j
  · exact ztable_32 j
  · exact ztable_33 j
  · exact ztable_34 j
  · exact ztable_35 j
  · exact ztable_36 j
  · exact ztable_37 j
  · exact ztable_38 j
  · exact ztable_39 j
  · exact ztable_40 j
  · exact ztable_41 j
  · exact ztable_42 j
  · exact ztable_43 j
  · exact ztable_44 j
lemma xones : ∀ j, ones (xmask j) ≤ 3 := by decide +kernel
lemma xcover_bits : ∀ i j, (xmask j).getLsbD i.val = true → j ∈ xneighbors i := by decide +kernel
lemma xcover (i : Fin 45) (j : Fin 90) (h : entry (xmask j) i = 1) : j ∈ xneighbors i := by
  apply xcover_bits i j
  cases hb : (xmask j).getLsbD i.val with
  | true => rfl
  | false =>
    have he : entry (xmask j) i = 0 := by dsimp only [entry]; rw [hb]; rfl
    rw [he] at h
    exact False.elim (zero_ne_one h)
def zv : Fin 90 → ZMod 2 := entry (BitVec.ofNat 90 206561871363)
def xv : Fin 90 → ZMod 2 := entry (BitVec.ofNat 90 619685614089)
def zvsupport : List (Fin 90) := [0, 1, 9, 10, 18, 19, 27, 28, 36, 37]
lemma zv_support : (Finset.univ.filter fun j => zv j ≠ 0) = zvsupport.toFinset := by decide +kernel
lemma zv_sig : signature xmask zvsupport = 0 := by decide +kernel
lemma zv_kernel : xH *ᵥ zv = 0 := by
  funext i
  change (xH *ᵥ zv) i = 0
  rw [support_mul,zv_support]
  change ∑ j ∈ zvsupport.toFinset, entry (xmask j) i = 0
  rw [← signature_entry xmask zvsupport (by decide +kernel) i,zv_sig]
  simp [entry]
lemma zv_weight : weight zv = 10 := by decide +kernel
def xvsupport : List (Fin 90) := [0, 3, 9, 12, 18, 21, 27, 30, 36, 39]
lemma xv_support : (Finset.univ.filter fun j => xv j ≠ 0) = xvsupport.toFinset := by decide +kernel
lemma xv_sig : signature zmask xvsupport = 0 := by decide +kernel
lemma xv_kernel : zH *ᵥ xv = 0 := by
  funext i
  change (zH *ᵥ xv) i = 0
  rw [support_mul,xv_support]
  change ∑ j ∈ xvsupport.toFinset, entry (zmask j) i = 0
  rw [← signature_entry zmask xvsupport (by decide +kernel) i,xv_sig]
  simp [entry]
lemma xv_weight : weight xv = 10 := by decide +kernel
lemma zx_dot : dotProduct zv xv = 1 := by decide +kernel
lemma row_orthogonal {r c : Type} [Fintype c]
    (H : Matrix r c (ZMod 2)) (v : c → ZMod 2) (hv : H *ᵥ v = 0)
    {w : c → ZMod 2} (hw : w ∈ rowSpace H) : dotProduct w v = 0 := by
  change w ∈ Submodule.span (ZMod 2) (Set.range H) at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i,rfl⟩ := hw
    exact congrFun hv i
  | zero => simp
  | add w u hw hu ihw ihu => simp [add_dotProduct, ihw, ihu]
  | smul a w hw ih => simp [smul_dotProduct, ih]

lemma weight_equiv {a b : Type} [Fintype a] [Fintype b]
    (e : a ≃ b) (v : b → ZMod 2) : weight (v ∘ e) = weight v := by
  classical
  simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact e.sum_comp (fun j => if v j ≠ 0 then (1 : ℕ) else 0)

lemma unindex_kernel (H : Matrix (Grp 15 3) (Qubit 15 3) (ZMod 2))
    (v : Fin 90 → ZMod 2) (hv : H.submatrix er eqb *ᵥ v = 0) :
    H *ᵥ (v ∘ eqb.symm) = 0 := by
  have h := Matrix.submatrix_mulVec_equiv H v er eqb
  rw [hv] at h
  funext i
  have hi := congrFun h (er.symm i)
  simpa using hi.symm

lemma index_kernel (H : Matrix (Grp 15 3) (Qubit 15 3) (ZMod 2))
    (v : Qubit 15 3 → ZMod 2) (hv : H *ᵥ v = 0) :
    H.submatrix er eqb *ᵥ (v ∘ eqb) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ eqb) ∘ eqb.symm = v := by funext i; simp
  rw [he,hv]
  rfl

lemma zlogical : IsZLogical polyA polyB (zv ∘ eqb.symm) := by
  constructor
  · apply unindex_kernel
    rw [xtable]
    exact zv_kernel
  · intro h
    have hx : HZ polyA polyB *ᵥ (xv ∘ eqb.symm) = 0 := by
      apply unindex_kernel
      rw [ztable]
      exact xv_kernel
    have hh := row_orthogonal (HZ polyA polyB) (xv ∘ eqb.symm) hx h
    rw [comp_equiv_dotProduct_comp_equiv, zx_dot] at hh
    exact one_ne_zero hh

lemma xlogical : IsXLogical polyA polyB (xv ∘ eqb.symm) := by
  constructor
  · apply unindex_kernel
    rw [ztable]
    exact xv_kernel
  · intro h
    have hz : HX polyA polyB *ᵥ (zv ∘ eqb.symm) = 0 := by
      apply unindex_kernel
      rw [xtable]
      exact zv_kernel
    have hh := row_orthogonal (HX polyA polyB) (zv ∘ eqb.symm) hz h
    rw [comp_equiv_dotProduct_comp_equiv, dotProduct_comm xv zv, zx_dot] at hh
    exact one_ne_zero hh

end BB90KernelData

set_option maxHeartbeats 0
open BB90Cert BB90Search
namespace BB90Direct

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) : ℕ → List (Fin n) → BitVec r → Bool
  | fuel, used, sy =>
    if sy = 0 then decide (fuel = 2) && decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => (nbr (pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr fuel (j :: used) (C j ^^^ sy)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) :
    check C K nbr fuel used sy = if sy = 0 then decide (fuel = 2) && decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => (nbr (pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr f (j::used) (C j ^^^ sy) := by
  cases fuel <;> rfl

lemma step {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r)
    (hs : sy ≠ 0)
    (hc : ∀ j ∈ nbr (pick sy), j ∉ used → check C K nbr fuel (j::used) (C j ^^^ sy) = true) :
    check C K nbr (fuel+1) used sy = true := by
  rw [check_eq,if_neg hs]
  change (nbr (pick sy)).all _ = true
  apply List.all_eq_true.mpr
  intro j hj
  by_cases hu : j ∈ used
  · simp [hu]
  · simpa only [if_neg hu] using hc j hj hu

lemma sound {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r)
    (h : check C K nbr fuel used sy = true) : BB90Search.check C K nbr fuel used sy = true := by
  induction fuel generalizing used sy with
  | zero =>
    rw [BB90Search.check_eq]
    split_ifs with hp hz
    · rfl
    · simpa [check,hz] using h
    · rfl
  | succ f ih =>
    rw [BB90Search.check_eq]
    by_cases hp : 3*(f+1) < ones sy
    · rw [if_pos hp]
    · rw [if_neg hp]
      by_cases hz : sy = 0
      · rw [if_pos hz]
        simpa [check,hz] using h
      · rw [if_neg hz]
        change (nbr (pick sy)).all _ = true
        have hh : ∀ j ∈ nbr (pick sy), (if j ∈ used then true else
            check C K nbr f (j::used) (C j ^^^ sy)) = true := by
          rw [check_eq,if_neg hz] at h
          simpa only [List.all_eq_true] using h
        apply List.all_eq_true.mpr
        intro j hj
        by_cases hu : j ∈ used
        · simp [hu]
        · have hhj := hh j hj
          rw [if_neg hu] at hhj
          simpa [hu] using ih (j::used) (C j ^^^ sy) hhj
end BB90Direct

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BB90Cert
namespace BB90Search

lemma completion_bound {r n : ℕ} (C : Fin n → BitVec r) (hC : ∀ j, ones (C j) ≤ 3)
    (T : Finset (Fin n)) (hT : ∀ i, ∑ j ∈ T, entry (C j) i = 0)
    (fuel : ℕ) (used : List (Fin n)) (hn : used.Nodup) (hu : used.toFinset ⊆ T)
    (hb : T.card ≤ used.length + fuel) : ones (signature C used) ≤ 3 * fuel := by
  classical
  let R := T \ used.toFinset
  let l := (List.finRange n).filter (fun j => j ∈ R)
  have hln : l.Nodup := (List.nodup_finRange n).filter _
  have hle : l.toFinset = R := by ext j; simp [l]
  have hlen : l.length = R.card := by rw [← hle,List.toFinset_card_of_nodup hln]
  have he : signature C l = signature C used := by
    apply entry_injective
    ext i
    rw [signature_entry C l hln i,hle,signature_entry C used hn i]
    dsimp only [R]
    have hs := Finset.sum_sdiff (f := fun j => entry (C j) i) hu
    rw [hT] at hs
    exact (eq_neg_of_add_eq_zero_left hs).trans (ZMod.neg_eq_self_mod_two _)
  have h := ones_sig_le C hC l
  rw [he,hlen] at h
  have hcard : R.card = T.card - used.length := by
    rw [Finset.card_sdiff_of_subset hu,List.toFinset_card_of_nodup hn]
  have hlecard : used.length ≤ T.card := by
    rw [← List.toFinset_card_of_nodup hn]
    exact Finset.card_le_card hu
  rw [hcard] at h
  omega

lemma extract {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (hC : ∀ j, ones (C j) ≤ 3)
    (hcover : ∀ i j, entry (C j) i = 1 → j ∈ nbr i)
    (T : Finset (Fin n)) (hT : ∀ i, ∑ j ∈ T, entry (C j) i = 0)
    (fuel : ℕ) (used : List (Fin n)) (hn : used.Nodup) (hu : used.toFinset ⊆ T)
    (hb : T.card ≤ used.length + fuel)
    (hc : check C K nbr fuel used (signature C used) = true) :
    ∃ S : Finset (Fin n), S ⊆ T ∧ used.toFinset ⊆ S ∧
      S.card = used.length + fuel - 2 ∧
      (∀ i, ∑ j ∈ S, entry (C j) i = 0) ∧ (∀ i, ∑ j ∈ S, entry (K j) i = 0) := by
  classical
  induction fuel using Nat.strong_induction_on generalizing used with
  | h fuel ih =>
    have hbound := completion_bound C hC T hT fuel used hn hu hb
    rw [check_eq,if_neg (by omega : ¬ 3*fuel < ones (signature C used))] at hc
    by_cases hz : signature C used = 0
    · have hh : fuel = 2 ∧ signature K used = 0 := by simpa [hz] using hc
      refine ⟨used.toFinset,hu,Finset.Subset.refl _,?_,?_,?_⟩
      · rw [List.toFinset_card_of_nodup hn,hh.1]; omega
      · intro i
        rw [← signature_entry C used hn i,hz]
        simp [entry]
      · intro i
        rw [← signature_entry K used hn i,hh.2]
        simp [entry]
    · cases fuel with
      | zero =>
        have he : used.toFinset = T := Finset.eq_of_subset_of_card_le hu (by
          rw [List.toFinset_card_of_nodup hn]; simpa using hb)
        apply False.elim
        apply hz
        apply entry_injective
        ext i
        rw [signature_entry C used hn i,he,hT]
        simp [entry]
      | succ f =>
        let i := pick (signature C used)
        have hp : entry (signature C used) i = 1 := by
          simp [entry,i,pick_spec _ hz]
        have hex : ∃ j ∈ T, j ∉ used ∧ entry (C j) i = 1 := by
          by_contra hnot
          have he : ∑ j ∈ used.toFinset, entry (C j) i = ∑ j ∈ T, entry (C j) i := by
            apply Finset.sum_subset hu
            intro j hj hjn
            by_contra hne
            exact hnot ⟨j,hj,by simpa using hjn,binary_eq_one hne⟩
          rw [← signature_entry C used hn i,hT,hp] at he
          exact one_ne_zero he
        obtain ⟨j,hj,hju,hji⟩ := hex
        have hjnbr := hcover i j hji
        have hall : (nbr i).all (fun j => if j ∈ used then true else
            check C K nbr f (j :: used) (C j ^^^ signature C used)) = true := by
          simpa only [hz,if_false] using hc
        have hchild := List.all_eq_true.mp hall j hjnbr
        rw [if_neg hju] at hchild
        have hsub : (j :: used).toFinset ⊆ T := by simpa using Finset.insert_subset hj hu
        obtain ⟨S,hST,hUS,hcard,hSC,hSK⟩ := ih f (by omega) (j::used)
          (List.nodup_cons.mpr ⟨hju,hn⟩) hsub (by simp only [List.length_cons]; omega)
          (by simpa only [signature,List.foldr_cons] using hchild)
        refine ⟨S,hST,?_,?_,hSC,hSK⟩
        · exact (Finset.subset_insert j used.toFinset).trans (by simpa using hUS)
        · simp only [List.length_cons] at hcard; omega
end BB90Search

set_option maxHeartbeats 0
open Matrix BBCode BB90Cert BB90Search
namespace BB90Search

lemma zero_small {r n : ℕ} (C : Fin n → BitVec r)
    (hi : Function.Injective C) (hn : ∀ j, C j ≠ 0)
    (T : Finset (Fin n)) (hc : T.card ≤ 2)
    (hT : ∀ i, ∑ j ∈ T, entry (C j) i = 0) : T = ∅ := by
  classical
  interval_cases hcard : T.card
  · exact Finset.card_eq_zero.mp hcard
  · obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hcard
    apply False.elim
    apply hn j
    apply entry_injective
    funext i
    have h := hT i
    simp only [Finset.sum_singleton] at h
    have hz : entry (0 : BitVec r) i = 0 := by simp [entry]
    simpa only [hz] using h

  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hcard
    have he : C i = C j := by
      apply entry_injective
      ext k
      have hh := hT k
      simp only [Finset.sum_pair hij] at hh
      exact (eq_neg_of_add_eq_zero_left hh).trans (ZMod.neg_eq_self_mod_two _)
    exact False.elim (hij (hi he))

lemma support_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (hC : ∀ j, ones (C j) ≤ 3)
    (hcover : ∀ i j, entry (C j) i = 1 → j ∈ nbr i)
    (hi : Function.Injective C) (hn : ∀ j, C j ≠ 0)
    (anchor : Fin n) (hc : check C K nbr 7 [anchor] (C anchor) = true)
    (T : Finset (Fin n)) (ha : anchor ∈ T) (hcard : T.card ≤ 8)
    (hT : ∀ i, ∑ j ∈ T, entry (C j) i = 0) :
    ∀ i, ∑ j ∈ T, entry (K j) i = 0 := by
  classical
  have hinit : check C K nbr 7 [anchor] (signature C [anchor]) = true := by
    simpa [signature] using hc
  obtain ⟨S,hST,hAS,hS,hSC,hSK⟩ := extract C K nbr hC hcover T hT 7 [anchor]
    (by simp) (by simpa) (by simpa) hinit
  have hR : T \ S = ∅ := by
    apply zero_small C hi hn (T \ S)
    · rw [Finset.card_sdiff_of_subset hST]
      simp only [List.length_singleton] at hS
      omega
    · intro i
      have hh := Finset.sum_sdiff (f := fun j => entry (C j) i) hST
      rw [hT,hSC,add_zero] at hh
      exact hh
  have he : S = T := Finset.Subset.antisymm hST (Finset.sdiff_eq_empty_iff_subset.mp hR)
  simpa [he] using hSK

lemma anchored_kernel {r n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec n)
    (nbr : Fin r → List (Fin n)) (hC : ∀ j, ones (C j) ≤ 3)
    (hcover : ∀ i j, entry (C j) i = 1 → j ∈ nbr i)
    (hi : Function.Injective C) (hn : ∀ j, C j ≠ 0)
    (anchor : Fin n) (hc : check C K nbr 7 [anchor] (C anchor) = true)
    (v : Fin n → ZMod 2) (ha : v anchor ≠ 0)
    (hweight : weight v ≤ 8) (hv : (Matrix.of fun i j => entry (C j) i) *ᵥ v = 0) :
    (Matrix.of fun i j => entry (K j) i) *ᵥ v = 0 := by
  classical
  let T := Finset.univ.filter fun j => v j ≠ 0
  have hz : ∀ i, ∑ j ∈ T, entry (C j) i = 0 := by
    intro i
    change ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), (Matrix.of fun i j => entry (C j) i) i j = 0
    rw [← support_mul (Matrix.of fun i j => entry (C j) i) v i,hv]
    rfl
  have hk := support_eq C K nbr hC hcover hi hn anchor hc T (by simpa [T] using ha) hweight hz
  ext i
  rw [support_mul]
  exact hk i
end BB90Search

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB90Cert BB90Search BB90KernelData
namespace BB90Pair
lemma pair_kernel (anchor j : Fin 90) (hj : j ≠ anchor)
    (hc : BB90Direct.check xmask xrem xneighbors 6 [j,anchor]
      (xmask j ^^^ xmask anchor) = true)
    (v : Fin 90 → ZMod 2) (ha : v anchor ≠ 0) (hvj : v j ≠ 0)
    (hw : weight v ≤ 8) (hv : xH *ᵥ v = 0) : xK *ᵥ v = 0 := by
  classical
  let T := Finset.univ.filter fun j => v j ≠ 0
  have hT : ∀ i, ∑ j ∈ T, entry (xmask j) i = 0 := by
    intro i
    change ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), xH i j = 0
    rw [← support_mul xH v i,hv]
    rfl
  have hn : [j,anchor].Nodup := by simpa using hj
  have hu : [j,anchor].toFinset ⊆ T := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl <;> simpa [T] using (by assumption : v _ ≠ 0)
  have hc' : BB90Search.check xmask xrem xneighbors 6 [j,anchor]
      (signature xmask [j,anchor]) = true := by
    simpa [signature] using BB90Direct.sound _ _ _ _ _ _ hc
  obtain ⟨S,hST,hAS,hS,hSC,hSK⟩ := extract xmask xrem xneighbors xones xcover T hT
    6 [j,anchor] hn hu (by change T.card ≤ 8; exact hw) hc'
  have hR : T \ S = ∅ := by
    apply zero_small xmask xinjective xnonzero (T \ S)
    · rw [Finset.card_sdiff_of_subset hST]
      have ht : T.card ≤ 8 := hw
      simp only [List.length_cons,List.length_nil] at hS
      omega
    · intro i
      have hh := Finset.sum_sdiff (f := fun j => entry (xmask j) i) hST
      rw [hT,hSC,add_zero] at hh
      exact hh
  have he : S = T := Finset.Subset.antisymm hST (Finset.sdiff_eq_empty_iff_subset.mp hR)
  ext i
  rw [support_mul]
  change ∑ j ∈ T, entry (xrem j) i = 0
  simpa only [he] using hSK i

lemma pair_mem (anchor j : Fin 90) (hj : j ≠ anchor)
    (hc : BB90Direct.check xmask xrem xneighbors 6 [j,anchor]
      (xmask j ^^^ xmask anchor) = true)
    (v : Qubit 15 3 → ZMod 2) (ha : v (eqb anchor) ≠ 0) (hvj : v (eqb j) ≠ 0)
    (hw : weight v ≤ 8) (hv : HX polyA polyB *ᵥ v = 0) : v ∈ rowSpace (HZ polyA polyB) := by
  have hwi : xH *ᵥ (v ∘ eqb) = 0 := by rw [← xtable]; exact index_kernel _ v hv
  have hweight : weight (v ∘ eqb) ≤ 8 := by rwa [weight_equiv]
  have hK := pair_kernel anchor j hj hc (v ∘ eqb) ha hvj hweight hwi
  have hdec : zH.transpose * xD + (1 : Matrix (Fin 90) (Fin 90) (ZMod 2)) * xK = 1 := by
    simpa only [Matrix.one_mul] using xdecomp
  have hmem := kernel_mem_row zH xD xK 1 hdec (v ∘ eqb) hK
  apply (rowspace_reindex (HZ polyA polyB) er eqb v).mp
  rwa [ztable]
end BB90Pair

open BB90Cert BB90Search BB90KernelData
namespace BB90KernelSearch
lemma anchor45_2_0_1 : BB90Direct.check xmask xrem xneighbors 4 [8, 6, 27, 45] 550628229440 = true := by decide +kernel
lemma anchor45_2_0_2 : BB90Direct.check xmask xrem xneighbors 4 [34, 6, 27, 45] 593510793472 = true := by decide +kernel
lemma anchor45_2_0_3 : BB90Direct.check xmask xrem xneighbors 4 [52, 6, 27, 45] 552708604162 = true := by decide +kernel
lemma anchor45_2_0_4 : BB90Direct.check xmask xrem xneighbors 4 [58, 6, 27, 45] 688000082176 = true := by decide +kernel
lemma anchor45_2_0_5 : BB90Direct.check xmask xrem xneighbors 4 [73, 6, 27, 45] 550296879360 = true := by decide +kernel
lemma anchor45_2_1_0 : BB90Direct.check xmask xrem xneighbors 4 [8, 25, 27, 45] 9346654142656 = true := by decide +kernel
lemma anchor45_2_1_1 : BB90Direct.check xmask xrem xneighbors 4 [24, 25, 27, 45] 13744734208000 = true := by decide +kernel
lemma anchor45_2_1_3 : BB90Direct.check xmask xrem xneighbors 4 [47, 25, 27, 45] 11545677398020 = true := by decide +kernel
lemma anchor45_2_1_4 : BB90Direct.check xmask xrem xneighbors 4 [71, 25, 27, 45] 9346655191072 = true := by decide +kernel
lemma anchor45_2_1_5 : BB90Direct.check xmask xrem xneighbors 4 [77, 25, 27, 45] 9350949111808 = true := by decide +kernel
lemma anchor45_2_2_0 : BB90Direct.check xmask xrem xneighbors 4 [7, 26, 27, 45] 18142747164992 = true := by decide +kernel
lemma anchor45_2_2_1 : BB90Direct.check xmask xrem xneighbors 4 [24, 26, 27, 45] 22540860784640 = true := by decide +kernel
lemma anchor45_2_2_3 : BB90Direct.check xmask xrem xneighbors 4 [46, 26, 27, 45] 19242258792450 = true := by decide +kernel
lemma anchor45_2_2_4 : BB90Direct.check xmask xrem xneighbors 4 [70, 26, 27, 45] 18142747688976 = true := by decide +kernel
lemma anchor45_2_2_5 : BB90Direct.check xmask xrem xneighbors 4 [76, 26, 27, 45] 18144894649344 = true := by decide +kernel
lemma anchor45_2_4_0 : BB90Direct.check xmask xrem xneighbors 4 [4, 69, 27, 45] 550565576736 = true := by decide +kernel
lemma anchor45_2_4_1 : BB90Direct.check xmask xrem xneighbors 4 [5, 69, 27, 45] 550569771024 = true := by decide +kernel
lemma anchor45_2_4_2 : BB90Direct.check xmask xrem xneighbors 4 [30, 69, 27, 45] 557003833344 = true := by decide +kernel
lemma anchor45_2_4_3 : BB90Direct.check xmask xrem xneighbors 4 [48, 69, 27, 45] 4948742111232 = true := by decide +kernel
lemma anchor45_2_4_4 : BB90Direct.check xmask xrem xneighbors 4 [54, 69, 27, 45] 559151317504 = true := by decide +kernel
lemma anchor45_2_5_0 : BB90Direct.check xmask xrem xneighbors 4 [10, 75, 27, 45] 551366428672 = true := by decide +kernel
lemma anchor45_2_5_1 : BB90Direct.check xmask xrem xneighbors 4 [11, 75, 27, 45] 551097992192 = true := by decide +kernel
lemma anchor45_2_5_2 : BB90Direct.check xmask xrem xneighbors 4 [36, 75, 27, 45] 963951722496 = true := by decide +kernel
lemma anchor45_2_5_3 : BB90Direct.check xmask xrem xneighbors 4 [54, 75, 27, 45] 560224796680 = true := by decide +kernel
lemma anchor45_2_5_4 : BB90Direct.check xmask xrem xneighbors 4 [60, 75, 27, 45] 1879080960 = true := by decide +kernel
lemma anchor45_4_0_0 : BB90Direct.check xmask xrem xneighbors 4 [6, 7, 51, 45] 550863110272 = true := by decide +kernel
lemma anchor45_4_0_2 : BB90Direct.check xmask xrem xneighbors 4 [35, 7, 51, 45] 576649691136 = true := by decide +kernel
lemma anchor45_4_0_3 : BB90Direct.check xmask xrem xneighbors 4 [53, 7, 51, 45] 555174854660 = true := by decide +kernel
lemma anchor45_4_0_4 : BB90Direct.check xmask xrem xneighbors 4 [59, 7, 51, 45] 825757810688 = true := by decide +kernel
lemma anchor45_4_0_5 : BB90Direct.check xmask xrem xneighbors 4 [74, 7, 51, 45] 551425146880 = true := by decide +kernel
lemma anchor45_4_1_0 : BB90Direct.check xmask xrem xneighbors 4 [6, 8, 51, 45] 550896664832 = true := by decide +kernel
lemma anchor45_4_1_2 : BB90Direct.check xmask xrem xneighbors 4 [34, 8, 51, 45] 593863114752 = true := by decide +kernel
lemma anchor45_4_1_3 : BB90Direct.check xmask xrem xneighbors 4 [52, 8, 51, 45] 553060925442 = true := by decide +kernel
lemma anchor45_4_1_4 : BB90Direct.check xmask xrem xneighbors 4 [58, 8, 51, 45] 688352403456 = true := by decide +kernel
lemma anchor45_4_1_5 : BB90Direct.check xmask xrem xneighbors 4 [73, 8, 51, 45] 551186071552 = true := by decide +kernel
lemma anchor45_4_2_0 : BB90Direct.check xmask xrem xneighbors 4 [6, 33, 51, 45] 602369163648 = true := by decide +kernel
lemma anchor45_4_2_1 : BB90Direct.check xmask xrem xneighbors 4 [25, 33, 51, 45] 9398529294336 = true := by decide +kernel
lemma anchor45_4_2_2 : BB90Direct.check xmask xrem xneighbors 4 [26, 33, 51, 45] 18194588762112 = true := by decide +kernel
lemma anchor45_4_2_4 : BB90Direct.check xmask xrem xneighbors 4 [69, 33, 51, 45] 602369425416 = true := by decide +kernel
lemma anchor45_4_2_5 : BB90Direct.check xmask xrem xneighbors 4 [75, 33, 51, 45] 601295421952 = true := by decide +kernel
lemma anchor45_4_4_0 : BB90Direct.check xmask xrem xneighbors 4 [13, 57, 51, 45] 621713309696 = true := by decide +kernel
lemma anchor45_4_4_1 : BB90Direct.check xmask xrem xneighbors 4 [14, 57, 51, 45] 623860785152 = true := by decide +kernel
lemma anchor45_4_4_2 : BB90Direct.check xmask xrem xneighbors 4 [39, 57, 51, 45] 3918100692992 = true := by decide +kernel
lemma anchor45_4_4_4 : BB90Direct.check xmask xrem xneighbors 4 [63, 57, 51, 45] 5017612582912 = true := by decide +kernel
lemma anchor45_4_4_5 : BB90Direct.check xmask xrem xneighbors 4 [78, 57, 51, 45] 628289961984 = true := by decide +kernel
lemma anchor45_4_5_0 : BB90Direct.check xmask xrem xneighbors 4 [3, 72, 51, 45] 550980550704 = true := by decide +kernel
lemma anchor45_4_5_1 : BB90Direct.check xmask xrem xneighbors 4 [22, 72, 51, 45] 1650500567040 = true := by decide +kernel
lemma anchor45_4_5_2 : BB90Direct.check xmask xrem xneighbors 4 [23, 72, 51, 45] 2750008000512 = true := by decide +kernel
lemma anchor45_4_5_3 : BB90Direct.check xmask xrem xneighbors 4 [66, 72, 51, 45] 550980583425 = true := by decide +kernel
lemma anchor45_4_5_5 : BB90Direct.check xmask xrem xneighbors 4 [87, 72, 51, 45] 5017746538496 = true := by decide +kernel
lemma anchor45_5_0_0 : BB90Direct.check xmask xrem xneighbors 4 [15, 16, 66, 45] 575544557568 = true := by decide +kernel
lemma anchor45_5_0_2 : BB90Direct.check xmask xrem xneighbors 4 [44, 16, 66, 45] 13761094090752 = true := by decide +kernel
lemma anchor45_5_0_3 : BB90Direct.check xmask xrem xneighbors 4 [62, 16, 66, 45] 2765977815040 = true := by decide +kernel
lemma anchor45_5_0_4 : BB90Direct.check xmask xrem xneighbors 4 [68, 16, 66, 45] 566962946052 = true := by decide +kernel
lemma anchor45_5_0_5 : BB90Direct.check xmask xrem xneighbors 4 [83, 16, 66, 45] 846127431680 = true := by decide +kernel
lemma anchor45_5_1_0 : BB90Direct.check xmask xrem xneighbors 4 [15, 17, 66, 45] 592724492288 = true := by decide +kernel
lemma anchor45_5_1_2 : BB90Direct.check xmask xrem xneighbors 4 [43, 17, 66, 45] 22574366982144 = true := by decide +kernel
lemma anchor45_5_1_3 : BB90Direct.check xmask xrem xneighbors 4 [61, 17, 66, 45] 1683646055424 = true := by decide +kernel
lemma anchor45_5_1_4 : BB90Direct.check xmask xrem xneighbors 4 [67, 17, 66, 45] 584138620930 = true := by decide +kernel
lemma anchor45_5_1_5 : BB90Direct.check xmask xrem xneighbors 4 [82, 17, 66, 45] 723720863744 = true := by decide +kernel
lemma anchor45_5_2_0 : BB90Direct.check xmask xrem xneighbors 4 [3, 42, 66, 45] 26938051657776 = true := by decide +kernel
lemma anchor45_5_2_1 : BB90Direct.check xmask xrem xneighbors 4 [22, 42, 66, 45] 28037571674112 = true := by decide +kernel
lemma anchor45_5_2_2 : BB90Direct.check xmask xrem xneighbors 4 [23, 42, 66, 45] 29137079107584 = true := by decide +kernel
lemma anchor45_5_2_4 : BB90Direct.check xmask xrem xneighbors 4 [72, 42, 66, 45] 26938185875520 = true := by decide +kernel
lemma anchor45_5_2_5 : BB90Direct.check xmask xrem xneighbors 4 [87, 42, 66, 45] 31404817645568 = true := by decide +kernel
lemma anchor45_5_3_0 : BB90Direct.check xmask xrem xneighbors 4 [10, 60, 66, 45] 287311872 = true := by decide +kernel
lemma anchor45_5_3_1 : BB90Direct.check xmask xrem xneighbors 4 [11, 60, 66, 45] 555746304 = true := by decide +kernel
lemma anchor45_5_3_2 : BB90Direct.check xmask xrem xneighbors 4 [36, 60, 66, 45] 412335734784 = true := by decide +kernel
lemma anchor45_5_3_3 : BB90Direct.check xmask xrem xneighbors 4 [54, 60, 66, 45] 8608808968 = true := by decide +kernel
lemma anchor45_5_3_5 : BB90Direct.check xmask xrem xneighbors 4 [75, 60, 66, 45] 1075838976 = true := by decide +kernel
lemma anchor45_5_5_0 : BB90Direct.check xmask xrem xneighbors 4 [3, 81, 66, 45] 619565809712 = true := by decide +kernel
lemma anchor45_5_5_1 : BB90Direct.check xmask xrem xneighbors 4 [22, 81, 66, 45] 1719085826048 = true := by decide +kernel
lemma anchor45_5_5_2 : BB90Direct.check xmask xrem xneighbors 4 [23, 81, 66, 45] 2818593259520 = true := by decide +kernel
lemma anchor45_5_5_4 : BB90Direct.check xmask xrem xneighbors 4 [72, 81, 66, 45] 619700027456 = true := by decide +kernel
lemma anchor45_5_5_5 : BB90Direct.check xmask xrem xneighbors 4 [87, 81, 66, 45] 4948892844032 = true := by decide +kernel
lemma anchor45_2_0 : BB90Direct.check xmask xrem xneighbors 5 [6, 27, 45] 550561120640 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (550561120640 : BitVec 45)) = [6, 8, 34, 52, 58, 73] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_2_0_1
    · exact anchor45_2_0_2
    · exact anchor45_2_0_3
    · exact anchor45_2_0_4
    · exact anchor45_2_0_5
lemma anchor45_2_1 : BB90Direct.check xmask xrem xneighbors 5 [25, 27, 45] 9346721251328 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (9346721251328 : BitVec 45)) = [8, 24, 25, 47, 71, 77] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_2_1_0
    · exact anchor45_2_1_1
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_2_1_3
    · exact anchor45_2_1_4
    · exact anchor45_2_1_5
lemma anchor45_2_2 : BB90Direct.check xmask xrem xneighbors 5 [26, 27, 45] 18142780719104 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (18142780719104 : BitVec 45)) = [7, 24, 26, 46, 70, 76] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_2_2_0
    · exact anchor45_2_2_1
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_2_2_3
    · exact anchor45_2_2_4
    · exact anchor45_2_2_5
lemma anchor45_2_4 : BB90Direct.check xmask xrem xneighbors 5 [69, 27, 45] 550561382408 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (550561382408 : BitVec 45)) = [4, 5, 30, 48, 54, 69] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_2_4_0
    · exact anchor45_2_4_1
    · exact anchor45_2_4_2
    · exact anchor45_2_4_3
    · exact anchor45_2_4_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor45_2_5 : BB90Direct.check xmask xrem xneighbors 5 [75, 27, 45] 551634862592 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (551634862592 : BitVec 45)) = [10, 11, 36, 54, 60, 75] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_2_5_0
    · exact anchor45_2_5_1
    · exact anchor45_2_5_2
    · exact anchor45_2_5_3
    · exact anchor45_2_5_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor45_2 : BB90Direct.check xmask xrem xneighbors 6 [27, 45] 550577897472 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (550577897472 : BitVec 45)) = [6, 25, 26, 45, 69, 75] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_2_0
    · exact anchor45_2_1
    · exact anchor45_2_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_2_4
    · exact anchor45_2_5
lemma anchor45_4_0 : BB90Direct.check xmask xrem xneighbors 5 [7, 51, 45] 550879887616 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (550879887616 : BitVec 45)) = [6, 7, 35, 53, 59, 74] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_4_0_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_4_0_2
    · exact anchor45_4_0_3
    · exact anchor45_4_0_4
    · exact anchor45_4_0_5
lemma anchor45_4_1 : BB90Direct.check xmask xrem xneighbors 5 [8, 51, 45] 550913441920 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (550913441920 : BitVec 45)) = [6, 8, 34, 52, 58, 73] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_4_1_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_4_1_2
    · exact anchor45_4_1_3
    · exact anchor45_4_1_4
    · exact anchor45_4_1_5
lemma anchor45_4_2 : BB90Direct.check xmask xrem xneighbors 5 [33, 51, 45] 602385940480 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (602385940480 : BitVec 45)) = [6, 25, 26, 45, 69, 75] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_4_2_0
    · exact anchor45_4_2_1
    · exact anchor45_4_2_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_4_2_4
    · exact anchor45_4_2_5
lemma anchor45_4_4 : BB90Direct.check xmask xrem xneighbors 5 [57, 51, 45] 619565813760 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (619565813760 : BitVec 45)) = [13, 14, 39, 57, 63, 78] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_4_4_0
    · exact anchor45_4_4_1
    · exact anchor45_4_4_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_4_4_4
    · exact anchor45_4_4_5
lemma anchor45_4_5 : BB90Direct.check xmask xrem xneighbors 5 [72, 51, 45] 550982647808 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (550982647808 : BitVec 45)) = [3, 22, 23, 66, 72, 87] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_4_5_0
    · exact anchor45_4_5_1
    · exact anchor45_4_5_2
    · exact anchor45_4_5_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_4_5_5
lemma anchor45_4 : BB90Direct.check xmask xrem xneighbors 6 [51, 45] 550846332992 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (550846332992 : BitVec 45)) = [7, 8, 33, 51, 57, 72] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_4_0
    · exact anchor45_4_1
    · exact anchor45_4_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_4_4
    · exact anchor45_4_5
lemma anchor45_5_0 : BB90Direct.check xmask xrem xneighbors 5 [16, 66, 45] 566954688512 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (566954688512 : BitVec 45)) = [15, 16, 44, 62, 68, 83] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_5_0_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_5_0_2
    · exact anchor45_5_0_3
    · exact anchor45_5_0_4
    · exact anchor45_5_0_5
lemma anchor45_5_1 : BB90Direct.check xmask xrem xneighbors 5 [17, 66, 45] 584134492160 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (584134492160 : BitVec 45)) = [15, 17, 43, 61, 67, 82] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_5_1_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_5_1_2
    · exact anchor45_5_1_3
    · exact anchor45_5_1_4
    · exact anchor45_5_1_5
lemma anchor45_5_2 : BB90Direct.check xmask xrem xneighbors 5 [42, 66, 45] 26938053754880 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (26938053754880 : BitVec 45)) = [3, 22, 23, 66, 72, 87] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_5_2_0
    · exact anchor45_5_2_1
    · exact anchor45_5_2_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_5_2_4
    · exact anchor45_5_2_5
lemma anchor45_5_3 : BB90Direct.check xmask xrem xneighbors 5 [60, 66, 45] 18874880 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (18874880 : BitVec 45)) = [10, 11, 36, 54, 60, 75] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_5_3_0
    · exact anchor45_5_3_1
    · exact anchor45_5_3_2
    · exact anchor45_5_3_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_5_3_5
lemma anchor45_5_5 : BB90Direct.check xmask xrem xneighbors 5 [81, 66, 45] 619567906816 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (619567906816 : BitVec 45)) = [3, 22, 23, 66, 72, 87] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_5_5_0
    · exact anchor45_5_5_1
    · exact anchor45_5_5_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_5_5_4
    · exact anchor45_5_5_5
lemma anchor45_5 : BB90Direct.check xmask xrem xneighbors 6 [66, 45] 549774721024 = true := by
  apply BB90Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (549774721024 : BitVec 45)) = [16, 17, 42, 60, 66, 81] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor45_5_0
    · exact anchor45_5_1
    · exact anchor45_5_2
    · exact anchor45_5_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor45_5_5
end BB90KernelSearch
theorem bound (v : BBCode.Qubit 15 3 → ZMod 2)
    (hv : BBCode.HX {(9, 0), (0, 1), (0, 2)} {(0, 0), (2, 0), (7, 0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 8)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (9, 0)) ≠ 0 ∨ v (Sum.inr (2, 0)) ≠ 0 ∨ v (Sum.inr (7, 0)) ≠ 0) :
    v ∈ BBCode.rowSpace (BBCode.HZ {(9, 0), (0, 1), (0, 2)} {(0, 0), (2, 0), (7, 0)}) := by
  rcases hb with h0 | h1 | h2
  · apply BB90Pair.pair_mem 45 27 (by decide +kernel) (by exact BB90KernelSearch.anchor45_2) v
    · simpa only [show BB90KernelData.eqb (45 : Fin 90) = (Sum.inr (0, 0)) from by decide +kernel] using ha
    · simpa only [show BB90KernelData.eqb (27 : Fin 90) = (Sum.inl (9, 0)) from by decide +kernel] using h0
    · exact hw
    · exact hv
  · apply BB90Pair.pair_mem 45 51 (by decide +kernel) (by exact BB90KernelSearch.anchor45_4) v
    · simpa only [show BB90KernelData.eqb (45 : Fin 90) = (Sum.inr (0, 0)) from by decide +kernel] using ha
    · simpa only [show BB90KernelData.eqb (51 : Fin 90) = (Sum.inr (2, 0)) from by decide +kernel] using h1
    · exact hw
    · exact hv
  · apply BB90Pair.pair_mem 45 66 (by decide +kernel) (by exact BB90KernelSearch.anchor45_5) v
    · simpa only [show BB90KernelData.eqb (45 : Fin 90) = (Sum.inr (0, 0)) from by decide +kernel] using ha
    · simpa only [show BB90KernelData.eqb (66 : Fin 90) = (Sum.inr (7, 0)) from by decide +kernel] using h2
    · exact hw
    · exact hv
end BB90Split_right_back

theorem solution (v : BBCode.Qubit 15 3 → ZMod 2)
    (hv : BBCode.HX {(9, 0), (0, 1), (0, 2)} {(0, 0), (2, 0), (7, 0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 8)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (9, 0)) ≠ 0 ∨ v (Sum.inr (2, 0)) ≠ 0 ∨ v (Sum.inr (7, 0)) ≠ 0) :
    v ∈ BBCode.rowSpace (BBCode.HZ {(9, 0), (0, 1), (0, 2)} {(0, 0), (2, 0), (7, 0)}) := BB90Split_right_back.bound v hv hw ha hb
#print axioms solution
