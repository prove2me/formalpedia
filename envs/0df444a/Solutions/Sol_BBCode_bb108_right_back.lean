-- Prove2me | solution 1 for BBCode.bb108_right_back
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T08:03:11.00478+00:00
-- url     : https://prove2.me/submissions/fb10e6d5-ce58-454d-ab55-4356f94814bb

import Definitions.Def_BBCode_Setting
open Matrix
namespace BB108Split_right_back
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BB108Cert

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

end BB108Cert

set_option maxHeartbeats 0
open Matrix BBCode BB108Cert
namespace BB108Bits

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
end BB108Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB108Cert BB108Bits
namespace BB108KernelData
def xmask (j : Fin 108) : BitVec 54 := BitVec.ofNat 54 (#[68719476784,137438953505,274877906947,549755813894,1099511627788,2199023255576,4398046514176,8796093024320,17592186044608,35184372089216,70368744178432,140737488356864,281474976907264,562949953556480,1125899906854912,2251799813709824,4503599627419648,9007199254839296,12582913,8650754,786436,1572872,3145744,6291488,805306432,553648256,50331904,100663808,201327616,402655232,51539611648,35433488384,3221241856,6442483712,12884967424,25769934848,3298535145472,2267743256576,206159478784,412318957568,824637915136,1649275830272,211106249310208,145135568420864,13194206642176,26388413284352,52776826568704,105553653137408,13510799955853312,9288676378935296,844429225099264,1688858450198528,3377716900397056,6755433800794112,285873023221768,571746046443536,1143492092887072,2286984185774081,4573968371548162,9147936743096324,281474976711169,562949953422338,1125899906844676,2251799813685320,4503599627370640,9007199254741280,32833,65666,131332,4616,9232,18464,2101312,4202624,8405248,295424,590848,1181696,134483968,268967936,537935872,18907136,37814272,75628544,8606973952,17213947904,34427895808,1210056704,2420113408,4840226816,550846332928,1101692665856,2203385331712,77443629056,154887258112,309774516224,35254165307392,70508330614784,141016661229568,4956392259584,9912784519168,19825569038336,2256266579673088,4512533159346176,9025066318692352,317209104613376,634418209226752,1268836418453504][j])
def xrow (i : Fin 54) : BitVec 108 := BitVec.ofNat 108 (#[75084012987521171462,150168025975042342924,300336051950084685848,599537196794072006704,1199074393588144013345,2398148787176288026627,4805376831201354973568,9610753662402709947136,19221507324805419894272,38370380594820608429056,76740761189641216854080,153481522379282433704128,307544117196886718308352,615088234393773436616704,1230176468787546873233408,2455704358068518939459584,4911408716137037878661120,9822817432274075757064192,19682823500600749971734528,39365647001201499943469056,78731294002402999886938112,157165078916385212125413376,314330157832770424234311680,628660315665540848452108288,1259700704038447998191009792,2519401408076895996382019584,5038802816153791992764039168,10058565050648653576026456064,20117130101297307150995947520,40234260202594614300934930432,80620845058460671884224626688,161241690116921343768449253376,322483380233842687536898506752,643748163241513828865693188096,1287496326483027657663740641280,2574992652966055315259835547648,5159734083741464986191866626049,10319468167482929972383733252098,20638936334965859944767466504196,41199882447456740932216288182280,82399764894913481860103249330192,164799529789826963715877171626016,5704427701027050347521952972864,11408855402054100695043905945728,22817710804108201390087811891456,40644047369817749511782354911744,81288094739635498746487779623936,162576189479270997215898629048320,40564819207304513472647479169024,81129638414609026945294958338048,162259276829218053890589916676096,5070602400922298604010625597440,10141204801844579475097718423552,20282409603689141217271904075776][i])
def xH : Matrix (Fin 54) (Fin 108) (ZMod 2) := fun i j => entry (xmask j) i
lemma xrow_bits : ∀ i j, (xrow i).getLsbD j.val = (xmask j).getLsbD i.val := by decide +kernel
lemma xrow_entry (i : Fin 54) (j : Fin 108) : entry (xrow i) j = xH i j := by
  change entry (xrow i) j = entry (xmask j) i
  unfold entry; rw [xrow_bits]
def zmask (j : Fin 108) : BitVec 54 := BitVec.ofNat 54 (#[4168,8336,16672,33281,66562,133124,266752,533504,1067008,2129984,4259968,8519936,17072128,34144256,68288512,136318976,272637952,545275904,1092616192,2185232384,4370464768,8724414464,17448828928,34897657856,69927436288,139854872576,279709745152,558362525696,1116725051392,2233450102784,4475355922432,8950711844864,17901423689728,35735201644544,71470403289088,142940806578176,286422779035648,572845558071296,1145691116142592,2287052905250816,4574105810501632,9148211621003264,316659348799489,633318697598978,1266637395197956,2256197860196360,4512395720392720,9024791440785440,2251799813685313,4503599627370626,9007199254741252,281474976711176,562949953422352,1125899906844704,262150,524300,1048600,2097200,4194337,8388611,16777600,33555200,67110400,134220800,268437568,536871104,1073766400,2147532800,4295065600,8590131200,17180004352,34359750656,68721049600,137442099200,274884198400,549768396800,1099520278528,2199024041984,4398147174400,8796294348800,17592588697600,35185177395200,70369297825792,140737538686976,281481419161600,562962838323200,1125925676646400,2251851353292800,4503635060850688,9007202475966464,412316860417,824633720834,1649267441668,3298534883336,2267742732304,206158430240,26388279066688,52776558133376,105553116266752,211106232533504,145135534867456,13194139535360,1688849860268032,3377699720536064,6755399441072128,13510798882144256,9288674231517184,844424930263040][j])
def zrow (i : Fin 54) : BitVec 108 := BitVec.ofNat 108 (#[1237940040150357276377481224,2475880079165807446657597456,4951760157196707787217829920,9903520314393415574435659777,19807040628786831148871319554,39614081257573662297742639108,79228162569604851289649316353,158456325066575647789067273218,316912650060517240787903186948,633825300121034481575806369864,1267650600242068963151612739728,2535301200484137926303225479456,5070602404454692468139046764609,10141204804260805429703286521986,20282409603873031352831766036740,40564819207746062705663531815432,81129638415492125411327063630864,162259276830984250822654127261728,226673609192141481840704,155838129963495315218560,14167171506202981974272,28334343012405947433472,56668686024811894866944,113337372049623789733888,14507110988297054837805056,9973640317663700173987840,906698976396990846353408,1813397952793980635742208,3626795905587961271484416,7253591811175922542968832,928455103251011509619523584,638312980330476811135221760,58028734489407414166618112,116057468978814760687501312,232114937957629521375002624,464229875915259042750005248,59421126608064736615649509376,40852030741150515912654192640,3713839007322074506663559168,7427678014644144684000083968,14855356029288289368000167936,29710712058576578736000335872,3802952102916143143401568600064,2614529967433633018409868328960,237685696468612768426467786752,475371392937225259776005373952,950742785874450519552010747904,1901485571748901039104021495808,243388934586633161177700390404096,167329917915752513178231573053440,15211884573991217179293938352128,30423769147982416625664343932928,60847538295964833251328687865856,121695076591929666502657375731712][i])
def zH : Matrix (Fin 54) (Fin 108) (ZMod 2) := fun i j => entry (zmask j) i
lemma zrow_bits : ∀ i j, (zrow i).getLsbD j.val = (zmask j).getLsbD i.val := by decide +kernel
lemma zrow_entry (i : Fin 54) (j : Fin 108) : entry (zrow i) j = zH i j := by
  change entry (zrow i) j = entry (zmask j) i
  unfold entry; rw [zrow_bits]
def xcoef (j : Fin 108) : BitVec 54 := BitVec.ofNat 54 (#[8,16,32,317286548247048,611964311839435,1183727576433485,317286548246536,611964311840459,1183727576435533,4957602316288,9915204632576,19830409265152,321127190663688,604252962366155,1168304877486925,317286548242432,611964311832283,1183727576419181,321127188529152,604252966487771,1168304885730157,2537741690606089,9915205223424,19830410446848,2291940712256009,604252693398235,1168304339551085,2572867008987208,37823504,75647008,35254167409217,9898054656016,19796109312032,2533901989843465,2420704256,4841408512,39652213920321,1101961633808,2203923267616,2256757416001608,612084801675979,1183968556106573,321127190630977,564051915055120,1128103830110240,0,0,0,4957602316360,2582782228337360,2592697432970080,0,0,0,2533902931759113,0,0,0,0,0,2572867023704640,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0][j])
def xrem (j : Fin 108) : BitVec 108 := BitVec.ofNat 108 (#[9903520314393415574435659776,19807040628786831148871319552,39614081257573662297742639104,249645603879950142779154352832512,179765266275262917917246046076928,40004591065888468193429432565760,249011778579829108297578546462720,178497615675020848954094433337344,37469289865404330267126207086592,3811426135235312920585385803776,2630259434845801026569398910976,267926034066777238537425125376,294006758125168366828341224800256,263494981930074541201018417315840,202471429539886889946372802347008,243931272655060026917464691441664,168336603830131265700441530302464,17147266180273743266395208024064,247727607664197845318950828638208,170936681012782077688812431998976,17354827709950542428535638720512,283390647942468004052974702690304,85027548606418125364543386288128,165062504079702337493697751416832,40425207357647626357861922111488,253333973867818984632360292581376,182149413122515267894843711422464,278181205267657464959092415004672,92558310890932781316643378692096,185116602736635324196302448754688,6320614810168365605724255944704,12791049237607197119548435202048,20589486296850242566723540615168,279595239575035483869008961208320,82397931168017246427541036597248,164794643441299232888086320906240,10123566913084508749056031326208,10176519270173564242015641665536,20351800600381630080051222413312,34324326966101727179245361299456,260853826948589033284793758908416,202259683594434018955434001432576,253512501499717665418690028371968,177506437185926068404114428002304,35563685174372829227079587332096,35184372088832,70368744177664,140737488355328,3900557818119310835605749891072,321701365244553865831335493369856,323954760186363684048517470355456,2251799813685248,4503599627370496,9007199254740992,319527160379373744500765999759360,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,324440563138440353562040513593344,2305843009213693952,4611686018427387904,9223372036854775808,18446744073709551616,36893488147419103232,73786976294838206464,147573952589676412928,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168,79228162514264337593543950336,158456325028528675187087900672,316912650057057350374175801344,633825300114114700748351602688,1267650600228229401496703205376,2535301200456458802993406410752,5070602400912917605986812821504,10141204801825835211973625643008,20282409603651670423947251286016,40564819207303340847894502572032,81129638414606681695789005144064,162259276829213363391578010288128][j])
def xD : Matrix (Fin 54) (Fin 108) (ZMod 2) := fun i j => entry (xcoef j) i
def xK : Matrix (Fin 108) (Fin 108) (ZMod 2) := fun i j => entry (xrem j) i
lemma xdecomp_bits : ∀ j, combination zrow (xcoef j) ^^^ xrem j = unit j := by decide +kernel
lemma xdecomp : zH.transpose * xD + xK = 1 := by
  have h := decomposition zrow xcoef xrem xdecomp_bits
  have he : (Matrix.of fun i j => entry (zrow i) j) = zH := by
    apply Matrix.ext; intro i j; exact zrow_entry i j
  rw [he] at h
  exact h
def decode (key : ℕ) : ℕ := (if key < 1101692665856 then (if key < 537935872 then (if key < 4202624 then (if key < 295424 then (if key < 32833 then (if key < 9232 then 69 else (if key < 18464 then 70 else 71)) else (if key < 65666 then 66 else (if key < 131332 then 67 else 68))) else (if key < 1181696 then (if key < 590848 then 75 else (if key < 786436 then 76 else 20)) else (if key < 2101312 then (if key < 1572872 then 77 else 21) else (if key < 3145744 then 72 else 22)))) else (if key < 50331904 then (if key < 8650754 then (if key < 6291488 then 73 else (if key < 8405248 then 23 else 74)) else (if key < 18907136 then (if key < 12582913 then 19 else 18) else (if key < 37814272 then 81 else 82))) else (if key < 134483968 then (if key < 75628544 then 26 else (if key < 100663808 then 83 else 27)) else (if key < 268967936 then (if key < 201327616 then 78 else 28) else (if key < 402655232 then 79 else 29))))) else (if key < 35433488384 then (if key < 4840226816 then (if key < 1210056704 then (if key < 553648256 then 80 else (if key < 805306432 then 25 else 24)) else (if key < 2420113408 then 87 else (if key < 3221241856 then 88 else 32))) else (if key < 12884967424 then (if key < 6442483712 then 89 else (if key < 8606973952 then 33 else 84)) else (if key < 25769934848 then (if key < 17213947904 then 34 else 85) else (if key < 34427895808 then 35 else 86)))) else (if key < 274877906947 then (if key < 77443629056 then (if key < 51539611648 then 31 else (if key < 68719476784 then 30 else 0)) else (if key < 154887258112 then (if key < 137438953505 then 93 else 1) else (if key < 206159478784 then 94 else 38))) else (if key < 549755813894 then (if key < 309774516224 then 2 else (if key < 412318957568 then 95 else 39)) else (if key < 824637915136 then (if key < 550846332928 then 3 else 90) else (if key < 1099511627788 then 40 else 4)))))) else (if key < 317209104613376 then (if key < 26388413284352 then (if key < 4398046514176 then (if key < 2203385331712 then (if key < 1649275830272 then 91 else (if key < 2199023255576 then 41 else 5)) else (if key < 2267743256576 then 92 else (if key < 3298535145472 then 37 else 36))) else (if key < 9912784519168 then (if key < 4956392259584 then 6 else (if key < 8796093024320 then 99 else 7)) else (if key < 17592186044608 then (if key < 13194206642176 then 100 else 44) else (if key < 19825569038336 then 8 else 101)))) else (if key < 140737488356864 then (if key < 52776826568704 then (if key < 35184372089216 then 45 else (if key < 35254165307392 then 9 else 96)) else (if key < 70508330614784 then (if key < 70368744178432 then 46 else 10) else (if key < 105553653137408 then 97 else 47))) else (if key < 211106249310208 then (if key < 141016661229568 then 11 else (if key < 145135568420864 then 98 else 43)) else (if key < 281474976907264 then (if key < 281474976711169 then 42 else 60) else (if key < 285873023221768 then 12 else 54))))) else (if key < 2256266579673088 then (if key < 1125899906844676 then (if key < 571746046443536 then (if key < 562949953422338 then 105 else (if key < 562949953556480 then 61 else 13)) else (if key < 634418209226752 then 55 else (if key < 844429225099264 then 106 else 50))) else (if key < 1268836418453504 then (if key < 1125899906854912 then 62 else (if key < 1143492092887072 then 14 else 56)) else (if key < 2251799813685320 then (if key < 1688858450198528 then 107 else 51) else (if key < 2251799813709824 then 63 else 15)))) else (if key < 6755433800794112 then (if key < 4503599627370640 then (if key < 2286984185774081 then 102 else (if key < 3377716900397056 then 57 else 52)) else (if key < 4512533159346176 then (if key < 4503599627419648 then 64 else 16) else (if key < 4573968371548162 then 103 else 58))) else (if key < 9025066318692352 then (if key < 9007199254741280 then 53 else (if key < 9007199254839296 then 65 else 17)) else (if key < 9288676378935296 then (if key < 9147936743096324 then 104 else 59) else (if key < 13510799955853312 then 49 else 48)))))))
lemma decode_left : ∀ j, decode (xmask j).toNat = j.val := by decide +kernel
lemma xinjective : Function.Injective xmask := by
  intro i j h
  apply Fin.ext
  rw [← decode_left i,← decode_left j,h]
lemma xnonzero : ∀ j, xmask j ≠ 0 := by decide +kernel
def xneighbors (i : Fin 54) : List (Fin 108) := #[[1,2,18,57,60,66],[2,3,19,58,61,67],[3,4,20,59,62,68],[4,5,21,54,63,69],[0,5,22,55,64,70],[0,1,23,56,65,71],[7,8,24,63,66,72],[8,9,25,64,67,73],[9,10,26,65,68,74],[10,11,27,60,69,75],[6,11,28,61,70,76],[6,7,29,62,71,77],[13,14,30,69,72,78],[14,15,31,70,73,79],[15,16,32,71,74,80],[16,17,33,66,75,81],[12,17,34,67,76,82],[12,13,35,68,77,83],[19,20,36,75,78,84],[20,21,37,76,79,85],[21,22,38,77,80,86],[22,23,39,72,81,87],[18,23,40,73,82,88],[18,19,41,74,83,89],[25,26,42,81,84,90],[26,27,43,82,85,91],[27,28,44,83,86,92],[28,29,45,78,87,93],[24,29,46,79,88,94],[24,25,47,80,89,95],[31,32,48,87,90,96],[32,33,49,88,91,97],[33,34,50,89,92,98],[34,35,51,84,93,99],[30,35,52,85,94,100],[30,31,53,86,95,101],[0,37,38,93,96,102],[1,38,39,94,97,103],[2,39,40,95,98,104],[3,40,41,90,99,105],[4,36,41,91,100,106],[5,36,37,92,101,107],[6,43,44,54,99,102],[7,44,45,55,100,103],[8,45,46,56,101,104],[9,46,47,57,96,105],[10,42,47,58,97,106],[11,42,43,59,98,107],[12,49,50,54,60,105],[13,50,51,55,61,106],[14,51,52,56,62,107],[15,52,53,57,63,102],[16,48,53,58,64,103],[17,48,49,59,65,104]][i]
def xnbr (i : Fin 54) (t : Fin 6) : Fin 108 := (xneighbors i).getD t.val 0
end BB108KernelData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB108Cert
namespace BB108Search

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
end BB108Search

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Matrix BBCode BB108Cert BB108Bits BB108Search
namespace BB108KernelData
def polyA : Poly 9 6 := {(3,0),(0,1),(0,2)}
def polyB : Poly 9 6 := {(0,3),(1,0),(2,0)}
def er : Fin 54 ≃ Grp 9 6 where
  toFun i := ((i.val / 6 : ℕ), (i.val % 6 : ℕ))
  invFun g := ⟨g.1.val * 6 + g.2.val, by
    have h1 := ZMod.val_lt g.1
    have h2 := ZMod.val_lt g.2
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eqb : Fin 108 ≃ Qubit 9 6 where
  toFun i := if h : i.val < 54 then Sum.inl (er ⟨i.val,h⟩)
    else Sum.inr (er ⟨i.val-54,by omega⟩)
  invFun q := match q with
    | Sum.inl g => ⟨(er.symm g).val, by have h := (er.symm g).isLt; omega⟩
    | Sum.inr g => ⟨54 + (er.symm g).val, by have h := (er.symm g).isLt; omega⟩
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
lemma ztable_45 : ∀ j, (HZ polyA polyB) (er 45) (eqb j) = zH 45 j := by decide +kernel
lemma ztable_46 : ∀ j, (HZ polyA polyB) (er 46) (eqb j) = zH 46 j := by decide +kernel
lemma ztable_47 : ∀ j, (HZ polyA polyB) (er 47) (eqb j) = zH 47 j := by decide +kernel
lemma ztable_48 : ∀ j, (HZ polyA polyB) (er 48) (eqb j) = zH 48 j := by decide +kernel
lemma ztable_49 : ∀ j, (HZ polyA polyB) (er 49) (eqb j) = zH 49 j := by decide +kernel
lemma ztable_50 : ∀ j, (HZ polyA polyB) (er 50) (eqb j) = zH 50 j := by decide +kernel
lemma ztable_51 : ∀ j, (HZ polyA polyB) (er 51) (eqb j) = zH 51 j := by decide +kernel
lemma ztable_52 : ∀ j, (HZ polyA polyB) (er 52) (eqb j) = zH 52 j := by decide +kernel
lemma ztable_53 : ∀ j, (HZ polyA polyB) (er 53) (eqb j) = zH 53 j := by decide +kernel
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
  · exact ztable_45 j
  · exact ztable_46 j
  · exact ztable_47 j
  · exact ztable_48 j
  · exact ztable_49 j
  · exact ztable_50 j
  · exact ztable_51 j
  · exact ztable_52 j
  · exact ztable_53 j
lemma xones : ∀ j, ones (xmask j) ≤ 3 := by decide +kernel
lemma xcover_bits : ∀ i j, (xmask j).getLsbD i.val = true → j ∈ xneighbors i := by decide +kernel
lemma xcover (i : Fin 54) (j : Fin 108) (h : entry (xmask j) i = 1) : j ∈ xneighbors i := by
  apply xcover_bits i j
  cases hb : (xmask j).getLsbD i.val with
  | true => rfl
  | false =>
    have he : entry (xmask j) i = 0 := by dsimp only [entry]; rw [hb]; rfl
    rw [he] at h
    exact False.elim (zero_ne_one h)
lemma weight_equiv {a b : Type} [Fintype a] [Fintype b]
    (e : a ≃ b) (v : b → ZMod 2) : weight (v ∘ e) = weight v := by
  classical
  simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact e.sum_comp (fun j => if v j ≠ 0 then (1 : ℕ) else 0)

lemma unindex_kernel (H : Matrix (Grp 9 6) (Qubit 9 6) (ZMod 2))
    (v : Fin 108 → ZMod 2) (hv : H.submatrix er eqb *ᵥ v = 0) :
    H *ᵥ (v ∘ eqb.symm) = 0 := by
  have h := Matrix.submatrix_mulVec_equiv H v er eqb
  rw [hv] at h
  funext i
  have hi := congrFun h (er.symm i)
  simpa using hi.symm

lemma index_kernel (H : Matrix (Grp 9 6) (Qubit 9 6) (ZMod 2))
    (v : Qubit 9 6 → ZMod 2) (hv : H *ᵥ v = 0) :
    H.submatrix er eqb *ᵥ (v ∘ eqb) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ eqb) ∘ eqb.symm = v := by funext i; simp
  rw [he,hv]
  rfl

end BB108KernelData

set_option maxHeartbeats 0
open BB108Cert BB108Search
namespace BB108Direct

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
    (h : check C K nbr fuel used sy = true) : BB108Search.check C K nbr fuel used sy = true := by
  induction fuel generalizing used sy with
  | zero =>
    rw [BB108Search.check_eq]
    split_ifs with hp hz
    · rfl
    · simpa [check,hz] using h
    · rfl
  | succ f ih =>
    rw [BB108Search.check_eq]
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
end BB108Direct

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BB108Cert
namespace BB108Search

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
end BB108Search

set_option maxHeartbeats 0
open Matrix BBCode BB108Cert BB108Search
namespace BB108Search

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
end BB108Search

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB108Cert BB108Search BB108KernelData
namespace BB108Pair
lemma pair_kernel (anchor j : Fin 108) (hj : j ≠ anchor)
    (hc : BB108Direct.check xmask xrem xneighbors 6 [j,anchor]
      (xmask j ^^^ xmask anchor) = true)
    (v : Fin 108 → ZMod 2) (ha : v anchor ≠ 0) (hvj : v j ≠ 0)
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
  have hc' : BB108Search.check xmask xrem xneighbors 6 [j,anchor]
      (signature xmask [j,anchor]) = true := by
    simpa [signature] using BB108Direct.sound _ _ _ _ _ _ hc
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

lemma pair_mem (anchor j : Fin 108) (hj : j ≠ anchor)
    (hc : BB108Direct.check xmask xrem xneighbors 6 [j,anchor]
      (xmask j ^^^ xmask anchor) = true)
    (v : Qubit 9 6 → ZMod 2) (ha : v (eqb anchor) ≠ 0) (hvj : v (eqb j) ≠ 0)
    (hw : weight v ≤ 8) (hv : HX polyA polyB *ᵥ v = 0) : v ∈ rowSpace (HZ polyA polyB) := by
  have hwi : xH *ᵥ (v ∘ eqb) = 0 := by rw [← xtable]; exact index_kernel _ v hv
  have hweight : weight (v ∘ eqb) ≤ 8 := by rwa [weight_equiv]
  have hK := pair_kernel anchor j hj hc (v ∘ eqb) ha hvj hweight hwi
  have hdec : zH.transpose * xD + (1 : Matrix (Fin 108) (Fin 108) (ZMod 2)) * xK = 1 := by
    simpa only [Matrix.one_mul] using xdecomp
  have hmem := kernel_mem_row zH xD xK 1 hdec (v ∘ eqb) hK
  apply (rowspace_reindex (HZ polyA polyB) er eqb v).mp
  rwa [ztable]
end BB108Pair

open BB108Cert BB108Search BB108KernelData
namespace BB108KernelSearch
lemma anchor54_2_0_0 : BB108Direct.check xmask xrem xneighbors 4 [3, 20, 21, 54] 286422780346370 = true := by decide +kernel
lemma anchor54_2_0_1 : BB108Direct.check xmask xrem xneighbors 4 [4, 20, 21, 54] 286972536160264 = true := by decide +kernel
lemma anchor54_2_0_3 : BB108Direct.check xmask xrem xneighbors 4 [59, 20, 21, 54] 9433809767628800 = true := by decide +kernel
lemma anchor54_2_0_4 : BB108Direct.check xmask xrem xneighbors 4 [62, 20, 21, 54] 1411772931377152 = true := by decide +kernel
lemma anchor54_2_0_5 : BB108Direct.check xmask xrem xneighbors 4 [68, 20, 21, 54] 285873024663808 = true := by decide +kernel
lemma anchor54_2_2_1 : BB108Direct.check xmask xrem xneighbors 4 [22, 37, 21, 54] 288140768051216 = true := by decide +kernel
lemma anchor54_2_2_2 : BB108Direct.check xmask xrem xneighbors 4 [38, 37, 21, 54] 288209485430784 = true := by decide +kernel
lemma anchor54_2_2_3 : BB108Direct.check xmask xrem xneighbors 4 [77, 37, 21, 54] 288140766087168 = true := by decide +kernel
lemma anchor54_2_2_4 : BB108Direct.check xmask xrem xneighbors 4 [80, 37, 21, 54] 288141302841344 = true := by decide +kernel
lemma anchor54_2_2_5 : BB108Direct.check xmask xrem xneighbors 4 [86, 37, 21, 54] 288175192801280 = true := by decide +kernel
lemma anchor54_2_3_0 : BB108Direct.check xmask xrem xneighbors 4 [6, 76, 21, 54] 281474977826816 = true := by decide +kernel
lemma anchor54_2_3_1 : BB108Direct.check xmask xrem xneighbors 4 [11, 76, 21, 54] 426610512691712 = true := by decide +kernel
lemma anchor54_2_3_2 : BB108Direct.check xmask xrem xneighbors 4 [28, 76, 21, 54] 285873225662464 = true := by decide +kernel
lemma anchor54_2_3_3 : BB108Direct.check xmask xrem xneighbors 4 [61, 76, 21, 54] 848822977757186 = true := by decide +kernel
lemma anchor54_2_3_4 : BB108Direct.check xmask xrem xneighbors 4 [70, 76, 21, 54] 285873024344080 = true := by decide +kernel
lemma anchor54_2_4_0 : BB108Direct.check xmask xrem xneighbors 4 [14, 79, 21, 54] 1411773199552512 = true := by decide +kernel
lemma anchor54_2_4_1 : BB108Direct.check xmask xrem xneighbors 4 [15, 79, 21, 54] 2537673106407424 = true := by decide +kernel
lemma anchor54_2_4_2 : BB108Direct.check xmask xrem xneighbors 4 [31, 79, 21, 54] 285908726185984 = true := by decide +kernel
lemma anchor54_2_4_3 : BB108Direct.check xmask xrem xneighbors 4 [70, 79, 21, 54] 285873292706832 = true := by decide +kernel
lemma anchor54_2_4_4 : BB108Direct.check xmask xrem xneighbors 4 [73, 79, 21, 54] 285873296900224 = true := by decide +kernel
lemma anchor54_2_5_1 : BB108Direct.check xmask xrem xneighbors 4 [22, 85, 21, 54] 285890238742544 = true := by decide +kernel
lemma anchor54_2_5_2 : BB108Direct.check xmask xrem xneighbors 4 [38, 85, 21, 54] 286096395075584 = true := by decide +kernel
lemma anchor54_2_5_3 : BB108Direct.check xmask xrem xneighbors 4 [77, 85, 21, 54] 285890236778496 = true := by decide +kernel
lemma anchor54_2_5_4 : BB108Direct.check xmask xrem xneighbors 4 [80, 85, 21, 54] 285890773532672 = true := by decide +kernel
lemma anchor54_2_5_5 : BB108Direct.check xmask xrem xneighbors 4 [86, 85, 21, 54] 285924663492608 = true := by decide +kernel
lemma anchor54_4_0_0 : BB108Direct.check xmask xrem xneighbors 4 [6, 7, 63, 54] 2542070883419136 = true := by decide +kernel
lemma anchor54_4_0_2 : BB108Direct.check xmask xrem xneighbors 4 [29, 7, 63, 54] 2546469332582400 = true := by decide +kernel
lemma anchor54_4_0_3 : BB108Direct.check xmask xrem xneighbors 4 [62, 7, 63, 54] 3672368836771844 = true := by decide +kernel
lemma anchor54_4_0_4 : BB108Direct.check xmask xrem xneighbors 4 [71, 7, 63, 54] 2546468929945632 = true := by decide +kernel
lemma anchor54_4_0_5 : BB108Direct.check xmask xrem xneighbors 4 [77, 7, 63, 54] 2546468931108864 = true := by decide +kernel
lemma anchor54_4_1_1 : BB108Direct.check xmask xrem xneighbors 4 [9, 8, 63, 54] 2590449395040512 = true := by decide +kernel
lemma anchor54_4_1_2 : BB108Direct.check xmask xrem xneighbors 4 [25, 8, 63, 54] 2555265576599552 = true := by decide +kernel
lemma anchor54_4_1_3 : BB108Direct.check xmask xrem xneighbors 4 [64, 8, 63, 54] 7058864650321936 = true := by decide +kernel
lemma anchor54_4_1_4 : BB108Direct.check xmask xrem xneighbors 4 [67, 8, 63, 54] 2555265023016962 = true := by decide +kernel
lemma anchor54_4_1_5 : BB108Direct.check xmask xrem xneighbors 4 [73, 8, 63, 54] 2555265027153920 = true := by decide +kernel
lemma anchor54_4_2_1 : BB108Direct.check xmask xrem xneighbors 4 [29, 24, 63, 54] 2537673507997696 = true := by decide +kernel
lemma anchor54_4_2_2 : BB108Direct.check xmask xrem xneighbors 4 [46, 24, 63, 54] 2590449931911168 = true := by decide +kernel
lemma anchor54_4_2_3 : BB108Direct.check xmask xrem xneighbors 4 [79, 24, 63, 54] 2537673374310400 = true := by decide +kernel
lemma anchor54_4_2_4 : BB108Direct.check xmask xrem xneighbors 4 [88, 24, 63, 54] 2537675525455872 = true := by decide +kernel
lemma anchor54_4_2_5 : BB108Direct.check xmask xrem xneighbors 4 [94, 24, 63, 54] 2537827992600576 = true := by decide +kernel
lemma anchor54_4_4_0 : BB108Direct.check xmask xrem xneighbors 4 [1, 66, 63, 54] 2537810275893280 = true := by decide +kernel
lemma anchor54_4_4_1 : BB108Direct.check xmask xrem xneighbors 4 [2, 66, 63, 54] 2537947714846722 = true := by decide +kernel
lemma anchor54_4_4_2 : BB108Direct.check xmask xrem xneighbors 4 [18, 66, 63, 54] 2537672849522688 = true := by decide +kernel
lemma anchor54_4_4_3 : BB108Direct.check xmask xrem xneighbors 4 [57, 66, 63, 54] 321057395343360 = true := by decide +kernel
lemma anchor54_4_4_4 : BB108Direct.check xmask xrem xneighbors 4 [60, 66, 63, 54] 2256197860229632 = true := by decide +kernel
lemma anchor54_4_5_0 : BB108Direct.check xmask xrem xneighbors 4 [13, 72, 63, 54] 3100622792556544 = true := by decide +kernel
lemma anchor54_4_5_1 : BB108Direct.check xmask xrem xneighbors 4 [14, 72, 63, 54] 3663572745854976 = true := by decide +kernel
lemma anchor54_4_5_2 : BB108Direct.check xmask xrem xneighbors 4 [30, 72, 63, 54] 2537724378611712 = true := by decide +kernel
lemma anchor54_4_5_3 : BB108Direct.check xmask xrem xneighbors 4 [69, 72, 63, 54] 2537672839004680 = true := by decide +kernel
lemma anchor54_4_5_5 : BB108Direct.check xmask xrem xneighbors 4 [78, 72, 63, 54] 2537672973484032 = true := by decide +kernel
lemma anchor54_5_0_0 : BB108Direct.check xmask xrem xneighbors 4 [9, 10, 69, 54] 391426139492480 = true := by decide +kernel
lemma anchor54_5_0_2 : BB108Direct.check xmask xrem xneighbors 4 [26, 10, 69, 54] 356241817735168 = true := by decide +kernel
lemma anchor54_5_0_3 : BB108Direct.check xmask xrem xneighbors 4 [65, 10, 69, 54] 9363441022144544 = true := by decide +kernel
lemma anchor54_5_0_4 : BB108Direct.check xmask xrem xneighbors 4 [68, 10, 69, 54] 356241767534596 = true := by decide +kernel
lemma anchor54_5_0_5 : BB108Direct.check xmask xrem xneighbors 4 [74, 10, 69, 54] 356241775808512 = true := by decide +kernel
lemma anchor54_5_1_0 : BB108Direct.check xmask xrem xneighbors 4 [6, 11, 69, 54] 422212465072128 = true := by decide +kernel
lemma anchor54_5_1_2 : BB108Direct.check xmask xrem xneighbors 4 [28, 11, 69, 54] 426610712907776 = true := by decide +kernel
lemma anchor54_5_1_3 : BB108Direct.check xmask xrem xneighbors 4 [61, 11, 69, 54] 989560465002498 = true := by decide +kernel
lemma anchor54_5_1_4 : BB108Direct.check xmask xrem xneighbors 4 [70, 11, 69, 54] 426610511589392 = true := by decide +kernel
lemma anchor54_5_1_5 : BB108Direct.check xmask xrem xneighbors 4 [76, 11, 69, 54] 426610512171008 = true := by decide +kernel
lemma anchor54_5_2_0 : BB108Direct.check xmask xrem xneighbors 4 [13, 27, 69, 54] 848823077437440 = true := by decide +kernel
lemma anchor54_5_2_1 : BB108Direct.check xmask xrem xneighbors 4 [14, 27, 69, 54] 1411773030735872 = true := by decide +kernel
lemma anchor54_5_2_2 : BB108Direct.check xmask xrem xneighbors 4 [30, 27, 69, 54] 285924663492608 = true := by decide +kernel
lemma anchor54_5_2_4 : BB108Direct.check xmask xrem xneighbors 4 [72, 27, 69, 54] 285873125982272 = true := by decide +kernel
lemma anchor54_5_2_5 : BB108Direct.check xmask xrem xneighbors 4 [78, 27, 69, 54] 285873258364928 = true := by decide +kernel
lemma anchor54_5_3_0 : BB108Direct.check xmask xrem xneighbors 4 [1, 60, 69, 54] 4535485468704 = true := by decide +kernel
lemma anchor54_5_3_1 : BB108Direct.check xmask xrem xneighbors 4 [2, 60, 69, 54] 4672924422146 = true := by decide +kernel
lemma anchor54_5_3_2 : BB108Direct.check xmask xrem xneighbors 4 [18, 60, 69, 54] 4398059098112 = true := by decide +kernel
lemma anchor54_5_3_3 : BB108Direct.check xmask xrem xneighbors 4 [57, 60, 69, 54] 2291382232289280 = true := by decide +kernel
lemma anchor54_5_3_5 : BB108Direct.check xmask xrem xneighbors 4 [66, 60, 69, 54] 4398046548032 = true := by decide +kernel
lemma anchor54_5_5_0 : BB108Direct.check xmask xrem xneighbors 4 [13, 75, 69, 54] 848822977069056 = true := by decide +kernel
lemma anchor54_5_5_1 : BB108Direct.check xmask xrem xneighbors 4 [14, 75, 69, 54] 1411772930367488 = true := by decide +kernel
lemma anchor54_5_5_2 : BB108Direct.check xmask xrem xneighbors 4 [30, 75, 69, 54] 285924563124224 = true := by decide +kernel
lemma anchor54_5_5_4 : BB108Direct.check xmask xrem xneighbors 4 [72, 75, 69, 54] 285873025613888 = true := by decide +kernel
lemma anchor54_5_5_5 : BB108Direct.check xmask xrem xneighbors 4 [78, 75, 69, 54] 285873157472256 = true := by decide +kernel
lemma anchor54_2_0 : BB108Direct.check xmask xrem xneighbors 5 [20, 21, 54] 285873024532484 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285873024532484 : BitVec 54)) = [3, 4, 20, 59, 62, 68] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_2_0_0
    · exact anchor54_2_0_1
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_2_0_3
    · exact anchor54_2_0_4
    · exact anchor54_2_0_5
lemma anchor54_2_2 : BB108Direct.check xmask xrem xneighbors 5 [37, 21, 54] 288140767002624 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (288140767002624 : BitVec 54)) = [21, 22, 38, 77, 80, 86] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_2_2_1
    · exact anchor54_2_2_2
    · exact anchor54_2_2_3
    · exact anchor54_2_2_4
    · exact anchor54_2_2_5
lemma anchor54_2_3 : BB108Direct.check xmask xrem xneighbors 5 [76, 21, 54] 285873024336896 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285873024336896 : BitVec 54)) = [6, 11, 28, 61, 70, 76] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_2_3_0
    · exact anchor54_2_3_1
    · exact anchor54_2_3_2
    · exact anchor54_2_3_3
    · exact anchor54_2_3_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor54_2_4 : BB108Direct.check xmask xrem xneighbors 5 [79, 21, 54] 285873292713984 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285873292713984 : BitVec 54)) = [14, 15, 31, 70, 73, 79] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_2_4_0
    · exact anchor54_2_4_1
    · exact anchor54_2_4_2
    · exact anchor54_2_4_3
    · exact anchor54_2_4_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor54_2_5 : BB108Direct.check xmask xrem xneighbors 5 [85, 21, 54] 285890237693952 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285890237693952 : BitVec 54)) = [21, 22, 38, 77, 80, 86] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_2_5_1
    · exact anchor54_2_5_2
    · exact anchor54_2_5_3
    · exact anchor54_2_5_4
    · exact anchor54_2_5_5
lemma anchor54_2 : BB108Direct.check xmask xrem xneighbors 6 [21, 54] 285873024794624 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285873024794624 : BitVec 54)) = [20, 21, 37, 76, 79, 85] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_2_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_2_2
    · exact anchor54_2_3
    · exact anchor54_2_4
    · exact anchor54_2_5
lemma anchor54_4_0 : BB108Direct.check xmask xrem xneighbors 5 [7, 63, 54] 2546468929931264 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (2546468929931264 : BitVec 54)) = [6, 7, 29, 62, 71, 77] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_4_0_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_4_0_2
    · exact anchor54_4_0_3
    · exact anchor54_4_0_4
    · exact anchor54_4_0_5
lemma anchor54_4_1 : BB108Direct.check xmask xrem xneighbors 5 [8, 63, 54] 2555265022951552 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (2555265022951552 : BitVec 54)) = [8, 9, 25, 64, 67, 73] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_4_1_1
    · exact anchor54_4_1_2
    · exact anchor54_4_1_3
    · exact anchor54_4_1_4
    · exact anchor54_4_1_5
lemma anchor54_4_2 : BB108Direct.check xmask xrem xneighbors 5 [24, 63, 54] 2537673642213376 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (2537673642213376 : BitVec 54)) = [24, 29, 46, 79, 88, 94] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_4_2_1
    · exact anchor54_4_2_2
    · exact anchor54_4_2_3
    · exact anchor54_4_2_4
    · exact anchor54_4_2_5
lemma anchor54_4_4 : BB108Direct.check xmask xrem xneighbors 5 [66, 63, 54] 2537672836939777 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (2537672836939777 : BitVec 54)) = [1, 2, 18, 57, 60, 66] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_4_4_0
    · exact anchor54_4_4_1
    · exact anchor54_4_4_2
    · exact anchor54_4_4_3
    · exact anchor54_4_4_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor54_4_5 : BB108Direct.check xmask xrem xneighbors 5 [72, 63, 54] 2537672839008256 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (2537672839008256 : BitVec 54)) = [13, 14, 30, 69, 72, 78] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_4_5_0
    · exact anchor54_4_5_1
    · exact anchor54_4_5_2
    · exact anchor54_4_5_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_4_5_5
lemma anchor54_4 : BB108Direct.check xmask xrem xneighbors 6 [63, 54] 2537672836907072 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (2537672836907072 : BitVec 54)) = [7, 8, 24, 63, 66, 72] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_4_0
    · exact anchor54_4_1
    · exact anchor54_4_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_4_4
    · exact anchor54_4_5
lemma anchor54_5_0 : BB108Direct.check xmask xrem xneighbors 5 [10, 69, 54] 356241767403776 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (356241767403776 : BitVec 54)) = [9, 10, 26, 65, 68, 74] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_5_0_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_5_0_2
    · exact anchor54_5_0_3
    · exact anchor54_5_0_4
    · exact anchor54_5_0_5
lemma anchor54_5_1 : BB108Direct.check xmask xrem xneighbors 5 [11, 69, 54] 426610511582208 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (426610511582208 : BitVec 54)) = [6, 11, 28, 61, 70, 76] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_5_1_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_5_1_2
    · exact anchor54_5_1_3
    · exact anchor54_5_1_4
    · exact anchor54_5_1_5
lemma anchor54_5_2 : BB108Direct.check xmask xrem xneighbors 5 [27, 69, 54] 285873123889152 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285873123889152 : BitVec 54)) = [13, 14, 30, 69, 72, 78] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_5_2_0
    · exact anchor54_5_2_1
    · exact anchor54_5_2_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_5_2_4
    · exact anchor54_5_2_5
lemma anchor54_5_3 : BB108Direct.check xmask xrem xneighbors 5 [60, 69, 54] 4398046515201 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (4398046515201 : BitVec 54)) = [1, 2, 18, 57, 60, 66] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_5_3_0
    · exact anchor54_5_3_1
    · exact anchor54_5_3_2
    · exact anchor54_5_3_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_5_3_5
lemma anchor54_5_5 : BB108Direct.check xmask xrem xneighbors 5 [75, 69, 54] 285873023520768 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285873023520768 : BitVec 54)) = [13, 14, 30, 69, 72, 78] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_5_5_0
    · exact anchor54_5_5_1
    · exact anchor54_5_5_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_5_5_4
    · exact anchor54_5_5_5
lemma anchor54_5 : BB108Direct.check xmask xrem xneighbors 6 [69, 54] 285873023226368 = true := by
  apply BB108Direct.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (pick (285873023226368 : BitVec 54)) = [10, 11, 27, 60, 69, 75] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor54_5_0
    · exact anchor54_5_1
    · exact anchor54_5_2
    · exact anchor54_5_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor54_5_5
end BB108KernelSearch
theorem bound (v : BBCode.Qubit 9 6 → ZMod 2)
    (hv : BBCode.HX {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 8)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (3, 3)) ≠ 0 ∨ v (Sum.inr (1, 3)) ≠ 0 ∨ v (Sum.inr (2, 3)) ≠ 0) :
    v ∈ BBCode.rowSpace (BBCode.HZ {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)}) := by
  rcases hb with h0 | h1 | h2
  · apply BB108Pair.pair_mem 54 21 (by decide +kernel) (by exact BB108KernelSearch.anchor54_2) v
    · simpa only [show BB108KernelData.eqb (54 : Fin 108) = (Sum.inr (0, 0)) from by decide +kernel] using ha
    · simpa only [show BB108KernelData.eqb (21 : Fin 108) = (Sum.inl (3, 3)) from by decide +kernel] using h0
    · exact hw
    · exact hv
  · apply BB108Pair.pair_mem 54 63 (by decide +kernel) (by exact BB108KernelSearch.anchor54_4) v
    · simpa only [show BB108KernelData.eqb (54 : Fin 108) = (Sum.inr (0, 0)) from by decide +kernel] using ha
    · simpa only [show BB108KernelData.eqb (63 : Fin 108) = (Sum.inr (1, 3)) from by decide +kernel] using h1
    · exact hw
    · exact hv
  · apply BB108Pair.pair_mem 54 69 (by decide +kernel) (by exact BB108KernelSearch.anchor54_5) v
    · simpa only [show BB108KernelData.eqb (54 : Fin 108) = (Sum.inr (0, 0)) from by decide +kernel] using ha
    · simpa only [show BB108KernelData.eqb (69 : Fin 108) = (Sum.inr (2, 3)) from by decide +kernel] using h2
    · exact hw
    · exact hv
end BB108Split_right_back

theorem solution (v : BBCode.Qubit 9 6 → ZMod 2)
    (hv : BBCode.HX {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 8)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (3, 3)) ≠ 0 ∨ v (Sum.inr (1, 3)) ≠ 0 ∨ v (Sum.inr (2, 3)) ≠ 0) :
    v ∈ BBCode.rowSpace (BBCode.HZ {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)}) := BB108Split_right_back.bound v hv hw ha hb
#print axioms solution
