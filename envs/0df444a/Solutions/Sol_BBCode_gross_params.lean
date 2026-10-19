-- Prove2me | solution 1 for BBCode.gross_params
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T08:36:38.638225+00:00
-- url     : https://prove2.me/submissions/b72ba2e5-4d19-4e32-a72d-d474fe26d727

import Definitions.Def_BBCode_Setting
import Theorems.Thm_BBCode_gross_small_kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BB144Cert

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

end BB144Cert

set_option maxHeartbeats 0
open Matrix BBCode BB144Cert
namespace BB144Bits

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
end BB144Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB144Cert BB144Bits
namespace BB144KernelData
def xmask (j : Fin 144) : BitVec 72 := BitVec.ofNat 72 (#[18014398509482032,36028797018964001,72057594037927939,144115188075855878,288230376151711756,576460752303423512,1152921504606850048,2305843009213696064,4611686018427388096,9223372036854776192,18446744073709552384,36893488147419104768,73786976294838403072,147573952589676548096,295147905179352838144,590295810358705676288,1180591620717411352576,2361183241434822705152,12582913,8650754,786436,1572872,3145744,6291488,805306432,553648256,50331904,100663808,201327616,402655232,51539611648,35433488384,3221241856,6442483712,12884967424,25769934848,3298535145472,2267743256576,206159478784,412318957568,824637915136,1649275830272,211106249310208,145135568420864,13194206642176,26388413284352,52776826568704,105553653137408,13510799955853312,9288676378935296,844429225099264,1688858450198528,3377716900397056,6755433800794112,864691197174611968,594475288251858944,54043470406352896,108086940812705792,216173881625411584,432347763250823168,55340236619175165952,38046418448118972416,3458782106006585344,6917564212013170688,13835128424026341376,27670256848052682752,3541775143627210620928,2434970780679614234624,221362054784421462016,442724109568842924032,885448219137685848064,1770896438275371696128,74939897799445053448,149879795598890106896,299759591197780213792,599519182395560427521,1199038364791120855042,2398076729582241710084,73786976294838206977,147573952589676413954,295147905179352827908,590295810358705651784,1180591620717411303568,2361183241434822607136,32833,65666,131332,4616,9232,18464,2101312,4202624,8405248,295424,590848,1181696,134483968,268967936,537935872,18907136,37814272,75628544,8606973952,17213947904,34427895808,1210056704,2420113408,4840226816,550846332928,1101692665856,2203385331712,77443629056,154887258112,309774516224,35254165307392,70508330614784,141016661229568,4956392259584,9912784519168,19825569038336,2256266579673088,4512533159346176,9025066318692352,317209104613376,634418209226752,1268836418453504,144401061099077632,288802122198155264,577604244396310528,20301382695256064,40602765390512128,81205530781024256,9241667910340968448,18483335820681936896,36966671641363873792,1299288492496388096,2598576984992776192,5197153969985552384,591466746261821980672,1182933492523643961344,2365866985047287922688,83154463519768838144,166308927039537676288,332617854079075352576][j])
def xrow (i : Fin 72) : BitVec 144 := BitVec.ofNat 144 (#[19682823500600681250947078,39365647001201362501894156,78731294002402725003788312,157165078916384662359113776,314330157832769324718227489,628660315665538649436454915,1259700704038443600060612992,2519401408076887200121225984,5038802816153774400242451968,10058565050648618390983281664,20117130101297236781966559296,40234260202594473563933114560,80620845058460390403879231488,161241690116920780807758462976,322483380233841561615516925952,643748163241511577022930026496,1287496326483023154045859794944,2574992652966046308091719331840,5159734083741464985848270815232,10319468167482929971696541630464,20638936334965859943393083260928,41199882447456740929467521695744,82399764894913481858935026876416,164799529789826963717870037237760,330222981359453759094289332174848,660445962718907518188578664349696,1320891925437815036377157328699392,2636792476637231419485921388527616,5273584953274462838971841720090624,10547169906548925677943682383216640,21134270807005040582034517259190272,42268541614010081164069034518380544,84537083228020162328138069036761088,168754718504782810847098968865767424,337509437009565621694197870085799936,675018874019131243388395672525864960,1352593331648322597250209104588177408,2705186663296645194500418209176354816,5410373326593290389000836418352709632,10800301984306099894214334007409115136,21600603968612199788428663685491195904,43201207937224399576857323041655357440,86565973225492646224013382693643354112,173131946450985292448026765387286708224,346263892901970584896053530774573416448,691219326995590393229717376474183368704,1382438653991180786459434475871436537856,2764877307982361572918868674665942876160,5540222286431529358336856492393174663168,11080444572863058716673712984786349326336,22160889145726117433347425969572698652672,44238036927717785166701912094347735597056,88476073855435570333403806455771938422784,176952147710871140666807595178620344074240,354574226331617878928836449030293533229057,709148452663235757857672898060587066458114,1418296905326471515715345796121174132916228,2831234363373938250631143442175297916502024,5662468726747876501262285749443489735639056,11324937453495753002524570363979873373913120,392005286692921109914536831773294265892928,784010573385842219829073663546588531785856,1568021146771684439658147327093177063571712,2793037667687062908145213049895131769995776,5586075335374125816290353465735473308632064,11172150670748251632580634297416156385904640,2787593149816327892999361327325341156380672,5575186299632655785998722654650682312761344,11150372599265311571997445309301364625522688,348449143727040989045667943964498393595904,696898287454081978086687308422421980184576,1393796574908163956168726037338269153361920][i])
def xH : Matrix (Fin 72) (Fin 144) (ZMod 2) := fun i j => entry (xmask j) i
lemma xrow_bits : ∀ i j, (xrow i).getLsbD j.val = (xmask j).getLsbD i.val := by decide +kernel
lemma xrow_entry (i : Fin 72) (j : Fin 144) : entry (xrow i) j = xH i j := by
  change entry (xrow i) j = entry (xmask j) i
  unfold entry; rw [xrow_bits]
def zmask (j : Fin 144) : BitVec 72 := BitVec.ofNat 72 (#[4168,8336,16672,33281,66562,133124,266752,533504,1067008,2129984,4259968,8519936,17072128,34144256,68288512,136318976,272637952,545275904,1092616192,2185232384,4370464768,8724414464,17448828928,34897657856,69927436288,139854872576,279709745152,558362525696,1116725051392,2233450102784,4475355922432,8950711844864,17901423689728,35735201644544,71470403289088,142940806578176,286422779035648,572845558071296,1145691116142592,2287052905250816,4574105810501632,9148211621003264,18331057858281472,36662115716562944,73324231433125888,146371385936052224,292742771872104448,585485543744208896,1173187702930014208,2346375405860028416,4692750811720056832,9367768699907342336,18735537399814684672,37471074799629369344,75084012987520909312,150168025975041818624,300336051950083637248,599537196794069909504,1199074393588139819008,2398148787176279638016,83010348331692982273,166020696663385964546,332041393326771929092,591448731863312498696,1182897463726624997392,2365794927453249994784,590295810358705651777,1180591620717411303554,2361183241434822607108,73786976294838206984,147573952589676413968,295147905179352827936,262150,524300,1048600,2097200,4194337,8388611,16777600,33555200,67110400,134220800,268437568,536871104,1073766400,2147532800,4295065600,8590131200,17180004352,34359750656,68721049600,137442099200,274884198400,549768396800,1099520278528,2199024041984,4398147174400,8796294348800,17592588697600,35185177395200,70369297825792,140737538686976,281481419161600,562962838323200,1125925676646400,2251851353292800,4503635060850688,9007202475966464,18014810826342400,36029621652684800,72059243305369600,144118486610739200,288232643894444032,576460958461853696,1152947892885913600,2305895785771827200,4611791571543654400,9223583143087308800,18446889209244418048,36893501341558636544,73788665144698470400,147577330289396940800,295154660578793881600,590309321157587763200,1180600909391642755072,2361184085859752738816,108086391056891905,216172782113783810,432345564227567620,864691128455135240,594475150812905488,54043195528445984,6917529027641081920,13835058055282163840,27670116110564327680,55340232221128655360,38046409652025951232,3458764513820542976,442721857769029242880,885443715538058485760,1770887431076116971520,3541774862152233943040,2434970217729660878848,221360928884514750464][j])
def zrow (i : Fin 72) : BitVec 144 := BitVec.ofNat 144 (#[85070591730234842614374727400357363720,170141183460469387719661034013066264592,340282366920938477930233647238484066336,680564733841876955860467294476968132609,1361129467683753911720934588953936265218,2722258935367507823441869177907872530436,5444517870735029922597616070753226064385,10889035741470040804613573211096950506498,21778071482940062568645487491784399390724,43556142965880125137290974983568798777416,87112285931760250274581949967137597554832,174224571863520500549163899934275195109664,348449143727041915041525062045336822906945,696898287454082611485823952544465541988482,1393796574908164004374421733542722980151556,2787593149816328008748843467085445960045064,5575186299632656017497686934170891920090128,11150372599265312034995373868341783840180256,59421126608064736064805277760,40852030741150514810965729408,3713839007322072303286632704,7427678014644144606556750336,14855356029288289213113500672,29710712058576578426227001344,3802952102916143108147537776640,2614529967433632947901806682112,237685696468612627410344493056,475371392937225254819632021504,950742785874450509639264043008,1901485571748901019278528086016,243388934586633158921442417704960,167329917915752508665715627655168,15211884573991208154262047555584,30423769147982416308456449376256,60847538295964832616912898752512,121695076591929665233825797505024,15576891813544522170972314733117440,10709114746608160554605800169930752,973560612735437321872771043557376,1947121225470874643741212760080384,3894242450941749287482425520160768,7788484901883498574964851040321536,996921076066849418942228142919516160,685383343782922275494771210875568128,62307879215067988599857346787672064,124615758430135977199437616645144576,249231516860271954398875233290289152,498463033720543908797750466580578304,63802948868278362812302601146849034240,43864534002107025631665357496036360192,3987704269764351270390870194411012096,7975408539528702540764007465289252864,15950817079057405081528014930578505728,31901634158114810163056029861157011456,4083388727569815219987366473398338191360,2807330176134849640426582879746327052288,255213073264918481305015692442304774144,510426146529836962608896477778512183296,1020852293059673925217792955557024366592,2041704586119347850435585911114048733184,261336878564468174079191454297493644247040,179669131272630376987301304303764931346432,16333636688954782803521004316307505545216,32667273377909565606969374577824779730944,65334546755819131213938749155649559461888,130669093511638262427877498311299118923776,16725560228125963141068253075039593231810560,11498824401448344127187283475440955606171648,1045352748093106099425344276243680354893824,2090705496186212198846039972980785902780416,4181410992372424397692079945961571805560832,8362821984744848795384159891923143611121664][i])
def zH : Matrix (Fin 72) (Fin 144) (ZMod 2) := fun i j => entry (zmask j) i
lemma zrow_bits : ∀ i j, (zrow i).getLsbD j.val = (zmask j).getLsbD i.val := by decide +kernel
lemma zrow_entry (i : Fin 72) (j : Fin 144) : entry (zrow i) j = zH i j := by
  change entry (zrow i) j = entry (zmask j) i
  unfold entry; rw [zrow_bits]
def xrows (i : Fin 66) : Fin 72 := ⟨#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,66,67][i], by fin_cases i <;> decide⟩
def xpiv (i : Fin 66) : Fin 144 := ⟨#[1,2,3,4,0,18,7,8,9,10,6,24,13,14,15,16,12,30,19,20,21,22,36,37,25,26,27,28,42,43,31,32,33,34,48,49,38,41,39,40,54,55,44,47,45,46,60,61,50,53,51,52,66,67,5,23,72,74,75,73,11,29,78,79,17,35][i], by fin_cases i <;> decide⟩
def xLmask (i : Fin 72) : BitVec 66 := BitVec.ofNat 66 (#[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808,13168645913573066459,15798828498051926893,18446744073709551616,36893488147419103232,36451723141426571409,43035408008477919161,24492679394676864930,48967621536493666053][i])
def xL : Matrix (Fin 72) (Fin 66) (ZMod 2) := fun i j => entry (xLmask i) j
def xR : Matrix (Fin 66) (Fin 144) (ZMod 2) := xH.submatrix xrows id
lemma xfactor_bits : ∀ i, combination (fun j => xrow (xrows j)) (xLmask i) = xrow i := by decide +kernel
lemma xfactor : xH = xL * xR := by
  have h := product xLmask (fun j => xrow (xrows j)) xrow xfactor_bits
  have he : (Matrix.of fun i j => entry (xrow i) j) = xH := by
    apply Matrix.ext; intro i j; exact xrow_entry i j
  have hr : (Matrix.of fun i j => entry (xrow (xrows i)) j) = xR := by
    apply Matrix.ext; intro i j; exact xrow_entry (xrows i) j
  rw [he,hr] at h
  exact h.symm
def xMmask (i : Fin 66) : BitVec 66 := BitVec.ofNat 66 (#[4899916394579099683,9223372036855037958,524300,90071992548458504,594475150815002640,180143985094819857,2240,16777600,33555200,5764607523101344256,10376293541595841536,2305843009213695040,143360,1073766400,2147532800,18446744078004551680,18446744082299551744,36893488147419172864,4980736,9961472,68722622464,36029071898968064,36029346774777888,137439215648,318767104,637534208,4398247837696,2305860601533956096,2305878193585784832,8796109801472,20401094656,40802189312,281487861612544,36894614055915880448,36895739947232919552,562951027294208,1168239493120,2542620639232,824633720832,687194767360,137443147776,12582912,74767327559680,162727720910848,52776558133248,43980465111040,8796361457664,805306368,4785108963819520,10414574138294272,3377699720527872,2814749767106560,562967133290496,51539607552,2199023255568,1,2,4,1099511627784,18017697044365312,72198331526284288,576460752303423552,144115188075856000,288230376151712000,4692750811720122368,9799832789158203392][i])
def xImask (i : Fin 66) : BitVec 66 := BitVec.ofNat 66 (#[36028797018963968,72057594037927936,144115188075855872,288231819277238272,18017284744019968,432345907832815620,3332665098658643988,16861744392537378611,8250748174347012284,13168588739119417051,13168623923776720667,14141569392965848935,48963399375335722757,24490146107001530274,48980287884676026117,24495775650559195042,24493523868998961058,72948896033459796135,12304099233175965459,432347007353094148,12304101432198434579,432345632948617220,12448213527894953751,12448215726918209303,10988916063064295183,14141499024775319399,10989056800569427727,14141551800914022247,6683564498924341352,6683423761435986024,72950021944104061095,72944392467118422183,72941014741628094631,72947770159322757287,12384944072683520,3377744817942528,12448216551555338007,12448214627406581527,12448214902284488471,12448215177162395415,1443125526528,2886234537984,6683370984357759080,6683494130180163688,6683546906738296936,6683529314552252520,92360033697792,184719010430976,6755421989892096,16888543700054016,13510843979526144,14636743886368768,5911042156658688,11822016667582464,576465081630457856,12304099782927585043,12015869544215875355,12250058374109990707,17474120211201788092,1026822089444950036,15798709750796127085,10988880879497512719,17654263990140799161,12232041639138037521,48976910210725117701,72952273795457353895][i])
def xInv : Matrix (Fin 66) (Fin 66) (ZMod 2) := fun i j => entry (xImask i) j
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
  have hu : (Matrix.of fun i j => entry (unit i) j) = (1 : Matrix (Fin 66) (Fin 66) (ZMod 2)) := by
    apply Matrix.ext; intro i j
    change entry (unit i) j = if i = j then 1 else 0
    rw [unit_entry]
    simp only [eq_comm]
  rw [hm,hu] at h
  exact h
lemma xrank : xH.rank = 66 := by
  apply Nat.le_antisymm
  · rw [xfactor]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)
  · have h := Matrix.rank_mul_le_left (xH.submatrix xrows xpiv) xInv
    rw [xminor,Matrix.rank_one,Fintype.card_fin] at h
    exact h.trans (Matrix.rank_submatrix_le _ _ _)
lemma xcolParity : ∀ j, ∑ i, xH i j = 1 := by decide +kernel
end BB144KernelData

set_option maxHeartbeats 0
open Matrix BBCode
namespace BB144Symmetry

variable {l m : ℕ}

def shiftG (g : Grp l m) : Grp l m ≃ Grp l m := Equiv.addRight g

def shiftQ (g : Grp l m) : Qubit l m ≃ Qubit l m :=
  Equiv.sumCongr (shiftG g) (shiftG g)

def negG : Grp l m ≃ Grp l m := Equiv.neg _

def dualQ : Qubit l m ≃ Qubit l m :=
  (Equiv.sumCongr negG negG).trans (Equiv.sumComm _ _)

lemma HX_shift (A B : Poly l m) (g : Grp l m) :
    (HX A B).submatrix (shiftG g) (shiftQ g) = HX A B := by
  ext i j
  cases j <;> simp [HX,BBCode.circulant,Matrix.submatrix,shiftG,shiftQ]

lemma HZ_shift (A B : Poly l m) (g : Grp l m) :
    (HZ A B).submatrix (shiftG g) (shiftQ g) = HZ A B := by
  ext i j
  cases j <;> simp [HZ,BBCode.circulant,Matrix.submatrix,shiftG,shiftQ]

lemma HZ_dual (A B : Poly l m) :
    (HZ A B).submatrix negG dualQ = HX A B := by
  ext i j
  cases j <;> simp [HX,HZ,BBCode.circulant,Matrix.submatrix,negG,dualQ,sub_eq_add_neg,add_comm]

lemma HX_dual (A B : Poly l m) :
    (HX A B).submatrix negG dualQ = HZ A B := by
  ext i j
  cases j <;> simp [HX,HZ,BBCode.circulant,Matrix.submatrix,negG,dualQ,sub_eq_add_neg,add_comm]

lemma kernel_reindex {r c : Type} [Fintype r] [Fintype c]
    (H : Matrix r c (ZMod 2)) (er : r ≃ r) (ec : c ≃ c) (v : c → ZMod 2)
    (hv : H *ᵥ v = 0) : H.submatrix er ec *ᵥ (v ∘ ec) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ ec) ∘ ec.symm = v := by ext j; simp
  rw [he,hv]
  rfl

lemma weight_equiv {a b : Type} [Fintype a] [Fintype b]
    (e : a ≃ b) (v : b → ZMod 2) : weight (v ∘ e) = weight v := by
  classical
  simp only [weight,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact e.sum_comp (fun j => if v j ≠ 0 then (1 : ℕ) else 0)

lemma x_to_z [NeZero l] [NeZero m] (A B : Poly l m) (v : Qubit l m → ZMod 2)
    (hv : IsXLogical A B v) : IsZLogical A B (v ∘ dualQ) := by
  constructor
  · have h := kernel_reindex (HZ A B) negG dualQ v hv.1
    rwa [HZ_dual] at h
  · intro h
    have he := (BB144Cert.rowspace_reindex (HX A B) negG dualQ v)
    rw [HX_dual] at he
    exact hv.2 (he.mp h)
end BB144Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB144Cert
namespace BB144Search

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
end BB144Search

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Matrix BBCode BB144Cert BB144Bits BB144Search
namespace BB144KernelData
def polyA : Poly 12 6 := {(3,0),(0,1),(0,2)}
def polyB : Poly 12 6 := {(0,3),(1,0),(2,0)}
def er : Fin 72 ≃ Grp 12 6 where
  toFun i := ((i.val / 6 : ℕ), (i.val % 6 : ℕ))
  invFun g := ⟨g.1.val * 6 + g.2.val, by
    have h1 := ZMod.val_lt g.1
    have h2 := ZMod.val_lt g.2
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eqb : Fin 144 ≃ Qubit 12 6 where
  toFun i := if h : i.val < 72 then Sum.inl (er ⟨i.val,h⟩)
    else Sum.inr (er ⟨i.val-72,by omega⟩)
  invFun q := match q with
    | Sum.inl g => ⟨(er.symm g).val, by have h := (er.symm g).isLt; omega⟩
    | Sum.inr g => ⟨72 + (er.symm g).val, by have h := (er.symm g).isLt; omega⟩
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
lemma xtable_45 : ∀ j, (HX polyA polyB) (er 45) (eqb j) = xH 45 j := by decide +kernel
lemma xtable_46 : ∀ j, (HX polyA polyB) (er 46) (eqb j) = xH 46 j := by decide +kernel
lemma xtable_47 : ∀ j, (HX polyA polyB) (er 47) (eqb j) = xH 47 j := by decide +kernel
lemma xtable_48 : ∀ j, (HX polyA polyB) (er 48) (eqb j) = xH 48 j := by decide +kernel
lemma xtable_49 : ∀ j, (HX polyA polyB) (er 49) (eqb j) = xH 49 j := by decide +kernel
lemma xtable_50 : ∀ j, (HX polyA polyB) (er 50) (eqb j) = xH 50 j := by decide +kernel
lemma xtable_51 : ∀ j, (HX polyA polyB) (er 51) (eqb j) = xH 51 j := by decide +kernel
lemma xtable_52 : ∀ j, (HX polyA polyB) (er 52) (eqb j) = xH 52 j := by decide +kernel
lemma xtable_53 : ∀ j, (HX polyA polyB) (er 53) (eqb j) = xH 53 j := by decide +kernel
lemma xtable_54 : ∀ j, (HX polyA polyB) (er 54) (eqb j) = xH 54 j := by decide +kernel
lemma xtable_55 : ∀ j, (HX polyA polyB) (er 55) (eqb j) = xH 55 j := by decide +kernel
lemma xtable_56 : ∀ j, (HX polyA polyB) (er 56) (eqb j) = xH 56 j := by decide +kernel
lemma xtable_57 : ∀ j, (HX polyA polyB) (er 57) (eqb j) = xH 57 j := by decide +kernel
lemma xtable_58 : ∀ j, (HX polyA polyB) (er 58) (eqb j) = xH 58 j := by decide +kernel
lemma xtable_59 : ∀ j, (HX polyA polyB) (er 59) (eqb j) = xH 59 j := by decide +kernel
lemma xtable_60 : ∀ j, (HX polyA polyB) (er 60) (eqb j) = xH 60 j := by decide +kernel
lemma xtable_61 : ∀ j, (HX polyA polyB) (er 61) (eqb j) = xH 61 j := by decide +kernel
lemma xtable_62 : ∀ j, (HX polyA polyB) (er 62) (eqb j) = xH 62 j := by decide +kernel
lemma xtable_63 : ∀ j, (HX polyA polyB) (er 63) (eqb j) = xH 63 j := by decide +kernel
lemma xtable_64 : ∀ j, (HX polyA polyB) (er 64) (eqb j) = xH 64 j := by decide +kernel
lemma xtable_65 : ∀ j, (HX polyA polyB) (er 65) (eqb j) = xH 65 j := by decide +kernel
lemma xtable_66 : ∀ j, (HX polyA polyB) (er 66) (eqb j) = xH 66 j := by decide +kernel
lemma xtable_67 : ∀ j, (HX polyA polyB) (er 67) (eqb j) = xH 67 j := by decide +kernel
lemma xtable_68 : ∀ j, (HX polyA polyB) (er 68) (eqb j) = xH 68 j := by decide +kernel
lemma xtable_69 : ∀ j, (HX polyA polyB) (er 69) (eqb j) = xH 69 j := by decide +kernel
lemma xtable_70 : ∀ j, (HX polyA polyB) (er 70) (eqb j) = xH 70 j := by decide +kernel
lemma xtable_71 : ∀ j, (HX polyA polyB) (er 71) (eqb j) = xH 71 j := by decide +kernel
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
  · exact xtable_45 j
  · exact xtable_46 j
  · exact xtable_47 j
  · exact xtable_48 j
  · exact xtable_49 j
  · exact xtable_50 j
  · exact xtable_51 j
  · exact xtable_52 j
  · exact xtable_53 j
  · exact xtable_54 j
  · exact xtable_55 j
  · exact xtable_56 j
  · exact xtable_57 j
  · exact xtable_58 j
  · exact xtable_59 j
  · exact xtable_60 j
  · exact xtable_61 j
  · exact xtable_62 j
  · exact xtable_63 j
  · exact xtable_64 j
  · exact xtable_65 j
  · exact xtable_66 j
  · exact xtable_67 j
  · exact xtable_68 j
  · exact xtable_69 j
  · exact xtable_70 j
  · exact xtable_71 j
def negIndex (i : Fin 72) : Fin 72 := ⟨#[0,5,4,3,2,1,66,71,70,69,68,67,60,65,64,63,62,61,54,59,58,57,56,55,48,53,52,51,50,49,42,47,46,45,44,43,36,41,40,39,38,37,30,35,34,33,32,31,24,29,28,27,26,25,18,23,22,21,20,19,12,17,16,15,14,13,6,11,10,9,8,7][i], by fin_cases i <;> decide⟩
def dualIndex (j : Fin 144) : Fin 144 := ⟨#[72,77,76,75,74,73,138,143,142,141,140,139,132,137,136,135,134,133,126,131,130,129,128,127,120,125,124,123,122,121,114,119,118,117,116,115,108,113,112,111,110,109,102,107,106,105,104,103,96,101,100,99,98,97,90,95,94,93,92,91,84,89,88,87,86,85,78,83,82,81,80,79,0,5,4,3,2,1,66,71,70,69,68,67,60,65,64,63,62,61,54,59,58,57,56,55,48,53,52,51,50,49,42,47,46,45,44,43,36,41,40,39,38,37,30,35,34,33,32,31,24,29,28,27,26,25,18,23,22,21,20,19,12,17,16,15,14,13,6,11,10,9,8,7][j], by fin_cases j <;> decide⟩
lemma er_neg : ∀ i, er (negIndex i) = -(er i) := by decide +kernel
lemma eqb_dual : ∀ j, eqb (dualIndex j) = BB144Symmetry.dualQ (eqb j) := by decide +kernel
lemma ztable_bits : ∀ i j, (xmask (dualIndex j)).getLsbD (negIndex i).val = (zmask j).getLsbD i.val := by decide +kernel
lemma ztable_entry (i : Fin 72) (j : Fin 144) : xH (negIndex i) (dualIndex j) = zH i j := by
  unfold xH zH entry
  rw [ztable_bits]
lemma ztable : (HZ polyA polyB).submatrix er eqb = zH := by
  apply Matrix.ext
  intro i j
  change HZ polyA polyB (er i) (eqb j) = zH i j
  have h := congrFun (congrFun (BB144Symmetry.HX_dual polyA polyB) (er i)) (eqb j)
  change HX polyA polyB (-(er i)) (BB144Symmetry.dualQ (eqb j)) = HZ polyA polyB (er i) (eqb j) at h
  rw [← h, ← er_neg, ← eqb_dual]
  change (HX polyA polyB).submatrix er eqb (negIndex i) (dualIndex j) = zH i j
  rw [xtable]
  exact ztable_entry i j
def zv : Fin 144 → ZMod 2 := entry (BitVec.ofNat 144 1555196755068351571297778519701173829695)
def zvsupport : List (Fin 144) := [0, 1, 2, 3, 4, 5, 55, 58, 121, 124, 127, 130]
lemma zv_support : (Finset.univ.filter fun j => zv j ≠ 0) = zvsupport.toFinset := by decide +kernel
lemma zv_sig : signature xmask zvsupport = 0 := by decide +kernel
lemma zv_kernel : xH *ᵥ zv = 0 := by
  funext i
  change (xH *ᵥ zv) i = 0
  rw [support_mul,zv_support]
  change ∑ j ∈ zvsupport.toFinset, entry (xmask j) i = 0
  rw [← signature_entry xmask zvsupport (by decide +kernel) i,zv_sig]
  simp [entry]
lemma zv_weight : weight zv = 12 := by decide +kernel
def xv : Fin 144 → ZMod 2 := entry (BitVec.ofNat 144 44566138923362110684630351872)
def xvsupport : List (Fin 144) := [20, 23, 26, 29, 72, 73, 74, 75, 76, 77, 92, 95]
lemma xv_support : (Finset.univ.filter fun j => xv j ≠ 0) = xvsupport.toFinset := by decide +kernel
lemma xv_sig : signature zmask xvsupport = 0 := by decide +kernel
lemma xv_kernel : zH *ᵥ xv = 0 := by
  funext i
  change (zH *ᵥ xv) i = 0
  rw [support_mul,xv_support]
  change ∑ j ∈ xvsupport.toFinset, entry (zmask j) i = 0
  rw [← signature_entry zmask xvsupport (by decide +kernel) i,xv_sig]
  simp [entry]
lemma xv_weight : weight xv = 12 := by decide +kernel
def zpair : Fin 144 → ZMod 2 := entry (BitVec.ofNat 144 1173474125726126152)
def zpairsupport : List (Fin 144) := [3, 6, 12, 15, 18, 24, 39, 42, 48, 51, 54, 60]
lemma zpair_support : (Finset.univ.filter fun j => zpair j ≠ 0) = zpairsupport.toFinset := by decide +kernel
lemma zpair_sig : signature zmask zpairsupport = 0 := by decide +kernel
lemma zpair_kernel : zH *ᵥ zpair = 0 := by
  funext i
  change (zH *ᵥ zpair) i = 0
  rw [support_mul,zpair_support]
  change ∑ j ∈ zpairsupport.toFinset, entry (zmask j) i = 0
  rw [← signature_entry zmask zpairsupport (by decide +kernel) i,zpair_sig]
  simp [entry]
def xpair : Fin 144 → ZMod 2 := entry (BitVec.ofNat 144 397536206985315487308546730926099222495232)
def xpairsupport : List (Fin 144) := [75, 84, 90, 96, 99, 102, 111, 120, 126, 132, 135, 138]
lemma xpair_support : (Finset.univ.filter fun j => xpair j ≠ 0) = xpairsupport.toFinset := by decide +kernel
lemma xpair_sig : signature xmask xpairsupport = 0 := by decide +kernel
lemma xpair_kernel : xH *ᵥ xpair = 0 := by
  funext i
  change (xH *ᵥ xpair) i = 0
  rw [support_mul,xpair_support]
  change ∑ j ∈ xpairsupport.toFinset, entry (xmask j) i = 0
  rw [← signature_entry xmask xpairsupport (by decide +kernel) i,xpair_sig]
  simp [entry]
lemma z_dot : dotProduct zv zpair = 1 := by decide +kernel
lemma x_dot : dotProduct xv xpair = 1 := by decide +kernel
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

lemma unindex_kernel (H : Matrix (Grp 12 6) (Qubit 12 6) (ZMod 2))
    (v : Fin 144 → ZMod 2) (hv : H.submatrix er eqb *ᵥ v = 0) :
    H *ᵥ (v ∘ eqb.symm) = 0 := by
  have h := Matrix.submatrix_mulVec_equiv H v er eqb
  rw [hv] at h
  funext i
  have hi := congrFun h (er.symm i)
  simpa using hi.symm

lemma index_kernel (H : Matrix (Grp 12 6) (Qubit 12 6) (ZMod 2))
    (v : Qubit 12 6 → ZMod 2) (hv : H *ᵥ v = 0) :
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
    have hx : HZ polyA polyB *ᵥ (zpair ∘ eqb.symm) = 0 := by
      apply unindex_kernel
      rw [ztable]
      exact zpair_kernel
    have hh := row_orthogonal (HZ polyA polyB) (zpair ∘ eqb.symm) hx h
    rw [comp_equiv_dotProduct_comp_equiv, z_dot] at hh
    exact one_ne_zero hh

lemma xlogical : IsXLogical polyA polyB (xv ∘ eqb.symm) := by
  constructor
  · apply unindex_kernel
    rw [ztable]
    exact xv_kernel
  · intro h
    have hz : HX polyA polyB *ᵥ (xpair ∘ eqb.symm) = 0 := by
      apply unindex_kernel
      rw [xtable]
      exact xpair_kernel
    have hh := row_orthogonal (HX polyA polyB) (xpair ∘ eqb.symm) hz h
    rw [comp_equiv_dotProduct_comp_equiv, x_dot] at hh
    exact one_ne_zero hh

end BB144KernelData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB144Cert BB144KernelData
namespace BB144Finish
private lemma lowerZ (v : Qubit 12 6 → ZMod 2) (hv : IsZLogical polyA polyB v) : 12 ≤ weight v := by
  by_contra hlt
  have hki : xH *ᵥ (v ∘ eqb) = 0 := by rw [← xtable]; exact index_kernel _ v hv.1
  have hd := kernel_even xH xcolParity (v ∘ eqb) hki
  rw [BB144KernelData.weight_equiv] at hd
  exact hv.2 (BBCode.gross_small_kernel v hv.1 (by omega))
private lemma lowerX (v : Qubit 12 6 → ZMod 2) (hv : IsXLogical polyA polyB v) : 12 ≤ weight v := by
  have h := lowerZ (v ∘ BB144Symmetry.dualQ) (BB144Symmetry.x_to_z _ _ _ hv)
  rwa [BB144Symmetry.weight_equiv] at h

theorem complete :
    IsCode (l := 12) (m := 6) {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} 144 12 12 := by
  change IsCode polyA polyB 144 12 12
  refine ⟨rfl,?_,?_,?_⟩
  · unfold NumLogical
    have hx : (HX polyA polyB).rank = 66 := by
      exact (Matrix.rank_submatrix (HX polyA polyB) er eqb).symm.trans
        ((congrArg Matrix.rank xtable).trans xrank)
    have hz : (HZ polyA polyB).rank = 66 :=
      ((congrArg Matrix.rank (BB144Symmetry.HX_dual polyA polyB)).symm.trans
        (Matrix.rank_submatrix (HX polyA polyB) BB144Symmetry.negG BB144Symmetry.dualQ)).trans hx
    exact congrArg₂ (fun a b : ℕ => a + b + 12) hx hz
  · refine ⟨⟨xv ∘ eqb.symm,xlogical,?_⟩,lowerX⟩
    rw [BB144KernelData.weight_equiv,xv_weight]
  · refine ⟨⟨zv ∘ eqb.symm,zlogical,?_⟩,lowerZ⟩
    rw [BB144KernelData.weight_equiv,zv_weight]
end BB144Finish


theorem solution : IsCode (l := 12) (m := 6) {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)} 144 12 12 := BB144Finish.complete
#print axioms solution
