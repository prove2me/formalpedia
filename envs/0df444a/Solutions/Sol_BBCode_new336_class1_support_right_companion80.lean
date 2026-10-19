-- Prove2me | solution 1 for BBCode.new336_class1_support_right_companion80
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:46:41.62293+00:00
-- url     : https://prove2.me/submissions/861bd150-0626-4855-9726-ed93613f6472

import Definitions.Def_BBCode_Setting
set_option maxErrors 1
open Matrix
namespace BB336Split_right_companion80
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BB336Cert

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

end BB336Cert

set_option maxHeartbeats 0
open Matrix BBCode BB336Cert
namespace BB336Bits

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
end BB336Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336Cert BB336Bits
namespace BB336KernelData
def xmask (j : Fin 336) : BitVec 168 := BitVec.ofNat 168 (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 11692013098647223345629488333136821074280857993217 else 23384026197294446691258957323460528314494920687619) else (if j.val < 3 then 46768052394588893382517914646921056628989841375238 else (if j.val < 4 then 93536104789177786765035829293842113257979682750476 else 187072209578355573530071658587684226515959365500952))) else (if j.val < 7 then (if j.val < 6 then 19342813113834066795298864 else 38685626227668133590597728) else (if j.val < 8 then 77371252455336267181195456 else (if j.val < 9 then 154742504910672534362390912 else 309485009821345068724781824)))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then 618970019642690137449563648 else 1237940039285380274899127296) else (if j.val < 13 then 2475880078570760549798254592 else (if j.val < 14 then 4951760157141521099596509184 else 9903520314283042199193018368))) else (if j.val < 18 then (if j.val < 16 then 19807040628566084398386036736 else (if j.val < 17 then 39614081257132168796772073472 else 79228162514264337593544146944)) else (if j.val < 19 then 158456325028528675187088293888 else (if j.val < 20 then 316912650057057350374176587776 else 633825300114114700748353175552))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then 1267650600228229401496706351104 else 2535301200456458802993412702208) else (if j.val < 24 then 5070602400912917605986825404416 else (if j.val < 25 then 10141204801825835211973650808832 else 20282409603651670423947301617664))) else (if j.val < 28 then (if j.val < 27 then 40564819207303340847894603235328 else 81129638414606681695789206470656) else (if j.val < 29 then 162259276829213363391578412941312 else (if j.val < 30 then 324518553658426726783156825882624 else 649037107316853453566313651765248)))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then 1298074214633706907132627303530496 else 2596148429267413814265254607060992) else (if j.val < 34 then 5192296858534827628530509214121984 else (if j.val < 35 then 10384593717069655257061018428243968 else 20769187434139310514122036856487936))) else (if j.val < 39 then (if j.val < 37 then 41538374868278621028244073712975872 else (if j.val < 38 then 83076749736557242056488147425951744 else 166153499473114484112976294851903488)) else (if j.val < 40 then 332306998946228968225952589703806976 else (if j.val < 41 then 664613997892457936451905179407613952 else 1329227995784915872903810358815227904)))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then 2658455991569831745807620717630455808 else 5316911983139663491615241435260911616) else (if j.val < 45 then 10633823966279326983230482870521823232 else (if j.val < 46 then 21267647932558653966460965741043646464 else 42535295865117307932921931482087292928))) else (if j.val < 49 then (if j.val < 48 then 85070591730234615865843862964174585856 else 170141183460469231731687725928349171712) else (if j.val < 50 then 340282366920938463463375451856698343424 else (if j.val < 51 then 680564733841876926926750903713396686848 else 1361129467683753853853501807426793373696)))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then 2722258935367507707707003614853586747392 else 5444517870735015415414007229707173494784) else (if j.val < 55 then 10889035741470030830828014459414346989568 else (if j.val < 56 then 21778071482940061661656028918828693979136 else 43556142965880123323312057837657387958272))) else (if j.val < 60 then (if j.val < 58 then 87112285931760246646624115675314775916544 else (if j.val < 59 then 174224571863520493293248231350629551833088 else 348449143727040986586496462701259103666176)) else (if j.val < 61 then 696898287454081973172992925402518207332352 else (if j.val < 62 then 1393796574908163946345985850805036414664704 else 2787593149816327892691971701610072829329408))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then 5575186299632655785383943403220145658658816 else 11150372599265311570767886806440291317317632) else (if j.val < 66 then 22300745198530623141535773612880582634635264 else (if j.val < 67 then 44601490397061246283071547225761165269270528 else 89202980794122492566143094451522330538541056))) else (if j.val < 70 then (if j.val < 69 then 178405961588244985132286188903044661077082112 else 356811923176489970264572377806089322154164224) else (if j.val < 71 then 713623846352979940529144755612178644308328448 else (if j.val < 72 then 1427247692705959881058289511224357288616656896 else 2854495385411919762116579022448714577233313792)))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then 5708990770823839524233158044897429154466627584 else 11417981541647679048466316089794858308933255168) else (if j.val < 76 then 22835963083295358096932632179589716617866510336 else (if j.val < 77 then 45671926166590716193865264359179433235733020672 else 91343852333181432387730528718358866471466041344))) else (if j.val < 81 then (if j.val < 79 then 182687704666362864775461057436717732942932082688 else (if j.val < 80 then 365375409332725729550922114873435465885864165376 else 730750818665451459101844229746870931771728330752)) else (if j.val < 82 then 1461501637330902918203688459493741863543456661504 else (if j.val < 83 then 2923003274661805836407376918987483727086913323008 else 5846006549323611672814753837974967454173826646016))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then 187072209578355573530071678534960250157340748152832 else 59237365161116829560602624) else (if j.val < 87 then 118474730322233659121205248 else (if j.val < 88 then 236949460644467318242410496 else 473898921288934636484820992))) else (if j.val < 91 then (if j.val < 90 then 928455029464035206174343169 else 1856910058928070412348686338) else (if j.val < 92 then 3713820117856140824697372676 else (if j.val < 93 then 7427640235712281649394745352 else 14855280471424563298789490704)))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then 29710560942849126597578981408 else 59421121885698253195157962816) else (if j.val < 97 then 118842243771396506390315925632 else (if j.val < 98 then 237684487542793012780631851264 else 475368975085586025561263702528))) else (if j.val < 102 then (if j.val < 100 then 950737950171172051122527405056 else (if j.val < 101 then 1901475900342344102245054810112 else 3802951800684688204490109620224)) else (if j.val < 103 then 7605903601369376408980219240448 else (if j.val < 104 then 15211807202738752817960438480896 else 30423614405477505635920876961792))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then 60847228810955011271841753923584 else 121694457621910022543683507847168) else (if j.val < 108 then 243388915243820045087367015694336 else (if j.val < 109 then 486777830487640090174734031388672 else 973555660975280180349468062777344))) else (if j.val < 112 then (if j.val < 111 then 1947111321950560360698936125554688 else 3894222643901120721397872251109376) else (if j.val < 113 then 7788445287802241442795744502218752 else (if j.val < 114 then 15576890575604482885591489004437504 else 31153781151208965771182978008875008)))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then 62307562302417931542365956017750016 else 124615124604835863084731912035500032) else (if j.val < 118 then 249230249209671726169463824071000064 else (if j.val < 119 then 498460498419343452338927648142000128 else 996920996838686904677855296284000256))) else (if j.val < 123 then (if j.val < 121 then 1993841993677373809355710592568000512 else (if j.val < 122 then 3987683987354747618711421185136001024 else 7975367974709495237422842370272002048)) else (if j.val < 124 then 15950735949418990474845684740544004096 else (if j.val < 125 then 31901471898837980949691369481088008192 else 63802943797675961899382738962176016384)))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then 127605887595351923798765477924352032768 else 255211775190703847597530955848704065536) else (if j.val < 129 then 510423550381407695195061911697408131072 else (if j.val < 130 then 1020847100762815390390123823394816262144 else 2041694201525630780780247646789632524288))) else (if j.val < 133 then (if j.val < 132 then 4083388403051261561560495293579265048576 else 8166776806102523123120990587158530097152) else (if j.val < 134 then 16333553612205046246241981174317060194304 else (if j.val < 135 then 32667107224410092492483962348634120388608 else 65334214448820184984967924697268240777216)))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then 130668428897640369969935849394536481554432 else 261336857795280739939871698789072963108864) else (if j.val < 139 then 522673715590561479879743397578145926217728 else (if j.val < 140 then 1045347431181122959759486795156291852435456 else 2090694862362245919518973590312583704870912))) else (if j.val < 144 then (if j.val < 142 then 4181389724724491839037947180625167409741824 else (if j.val < 143 then 8362779449448983678075894361250334819483648 else 16725558898897967356151788722500669638967296)) else (if j.val < 145 then 33451117797795934712303577445001339277934592 else (if j.val < 146 then 66902235595591869424607154890002678555869184 else 133804471191183738849214309780005357111738368))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then 267608942382367477698428619560010714223476736 else 535217884764734955396857239120021428446953472) else (if j.val < 150 then 1070435769529469910793714478240042856893906944 else (if j.val < 151 then 2140871539058939821587428956480085713787813888 else 4281743078117879643174857912960171427575627776))) else (if j.val < 154 then (if j.val < 153 then 8563486156235759286349715825920342855151255552 else 17126972312471518572699431651840685710302511104) else (if j.val < 155 then 34253944624943037145398863303681371420605022208 else (if j.val < 156 then 68507889249886074290797726607362742841210044416 else 137015778499772148581595453214725485682420088832)))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 274031556999544297163190906429450971364840177664 else 548063113999088594326381812858901942729680355328) else (if j.val < 160 then 1096126227998177188652763625717803885459360710656 else (if j.val < 161 then 2192252455996354377305527251435607770918721421312 else 4384504911992708754611054502871215541837442842624))) else (if j.val < 165 then (if j.val < 163 then 8769009823985417509222109005742431083674885685248 else (if j.val < 164 then 17538019647970835018444218011484862167349771370496 else 35076039295941670036888436022969724334699542740992)) else (if j.val < 166 then 70152078591883340073776872045939448669399085481984 else (if j.val < 167 then 140304157183766680147553744091878897338798170963968 else 280608314367533360295107488183757794677596341927936)))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then 1208925819614629178900481 else 2417851639229258357800962) else (if j.val < 171 then 4835703278458516715601924 else (if j.val < 172 then 9671406556917033431203848 else 67108881))) else (if j.val < 175 then (if j.val < 174 then 134217762 else 268435524) else (if j.val < 176 then 536871048 else (if j.val < 177 then 1073742096 else 2147484192)))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then 4294968384 else 8589936768) else (if j.val < 181 then 17179873536 else (if j.val < 182 then 34359747072 else 68719494144))) else (if j.val < 186 then (if j.val < 184 then 137438988288 else (if j.val < 185 then 274877976576 else 549755953152)) else (if j.val < 187 then 1099511906304 else (if j.val < 188 then 2199023812608 else 4398047625216))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then 8796095250432 else 17592190500864) else (if j.val < 192 then 35184381001728 else (if j.val < 193 then 70368762003456 else 140737524006912))) else (if j.val < 196 then (if j.val < 195 then 281475048013824 else 562950096027648) else (if j.val < 197 then 1125900192055296 else (if j.val < 198 then 2251800384110592 else 4503600768221184)))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then 9007201536442368 else 18014403072884736) else (if j.val < 202 then 36028806145769472 else (if j.val < 203 then 72057612291538944 else 144115224583077888))) else (if j.val < 207 then (if j.val < 205 then 288230449166155776 else (if j.val < 206 then 576460898332311552 else 1152921796664623104)) else (if j.val < 208 then 2305843593329246208 else (if j.val < 209 then 4611687186658492416 else 9223374373316984832)))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then 18446748746633969664 else 36893497493267939328) else (if j.val < 213 then 73786994986535878656 else (if j.val < 214 then 147573989973071757312 else 295147979946143514624))) else (if j.val < 217 then (if j.val < 216 then 590295959892287029248 else 1180591919784574058496) else (if j.val < 218 then 2361183839569148116992 else (if j.val < 219 then 4722367679138296233984 else 9444735358276592467968)))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then 18889470716553184935936 else 37778941433106369871872) else (if j.val < 223 then 75557882866212739743744 else (if j.val < 224 then 151115765732425479487488 else 302231531464850958974976))) else (if j.val < 228 then (if j.val < 226 then 604463062929701917949952 else (if j.val < 227 then 1208926125859403835899904 else 2417852251718807671799808)) else (if j.val < 229 then 4835704503437615343599616 else (if j.val < 230 then 9671409006875230687199232 else 4899916394579099649))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then 9799832789158199298 else 19599665578316398596) else (if j.val < 234 then 39199331156632797192 else (if j.val < 235 then 78398662313265594384 else 156797324626531188768))) else (if j.val < 238 then (if j.val < 237 then 313594649253062377536 else 627189298506124755072) else (if j.val < 239 then 1254378597012249510144 else (if j.val < 240 then 2508757194024499020288 else 5017514388048998040576)))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then 10035028776097996081152 else 20070057552195992162304) else (if j.val < 244 then 40140115104391984324608 else (if j.val < 245 then 80280230208783968649216 else 160560460417567937298432))) else (if j.val < 249 then (if j.val < 247 then 321120920835135874596864 else (if j.val < 248 then 642241841670271749193728 else 1284483683340543498387456)) else (if j.val < 250 then 2568967366681086996774912 else (if j.val < 251 then 5137934733362173993549824 else 10275869466724347987099648))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then 23384026197294446772388615080880323844350721130496 else 46768052394588893544777230161760647688701442260992) else (if j.val < 255 then 93536104789177787089554460323521295377402884521984 else (if j.val < 256 then 187072209578355574179108920647042590754805769043968 else 1298074543461529842311759602384896))) else (if j.val < 259 then (if j.val < 258 then 2596149086923059684623519204769792 else 5192298173846119369247038409539584) else (if j.val < 260 then 10384596347692238738494076819079168 else (if j.val < 261 then 20769192695384477476988153638158336 else 41538385390768954953976307276316672)))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then 83076770781537909907952614552633344 else 166153541563075819815905229105266688) else (if j.val < 265 then 332307083126151639631810458210533376 else (if j.val < 266 then 664614166252303279263620916421066752 else 1329228332504606558527241832842133504))) else (if j.val < 270 then (if j.val < 268 then 2658456665009213117054483665684267008 else (if j.val < 269 then 5316913330018426234108967331368534016 else 10633826660036852468217934662737068032)) else (if j.val < 271 then 21267653320073704936435869325474136064 else (if j.val < 272 then 42535306640147409872871738650948272128 else 85070613280294819745743477301896544256))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then 170141226560589639491486954603793088512 else 340282453121179278982973909207586177024) else (if j.val < 276 then 680564906242358557965947818415172354048 else (if j.val < 277 then 1361129812484717115931895636830344708096 else 2722259624969434231863791273660689416192))) else (if j.val < 280 then (if j.val < 279 then 5444519249938868463727582547321378832384 else 10889038499877736927455165094642757664768) else (if j.val < 281 then 21778076999755473854910330189285515329536 else (if j.val < 282 then 43556153999510947709820660378571030659072 else 87112307999021895419641320757142061318144)))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then 174224615998043790839282641514284122636288 else 348449231996087581678565283028568245272576) else (if j.val < 286 then 696898463992175163357130566057136490545152 else (if j.val < 287 then 1393796927984350326714261132114272981090304 else 2787593855968700653428522264228545962180608))) else (if j.val < 291 then (if j.val < 289 then 5575187711937401306857044528457091924361216 else (if j.val < 290 then 11150375423874802613714089056914183848722432 else 22300750847749605227428178113828367697444864)) else (if j.val < 292 then 44601501695499210454856356227656735394889728 else (if j.val < 293 then 89203003390998420909712712455313470789779456 else 178406006781996841819425424910626941579558912)))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then 356812013563993683638850849821253883159117824 else 713624027127987367277701699642507766318235648) else (if j.val < 297 then 1427248054255974734555403399285015532636471296 else (if j.val < 298 then 2854496108511949469110806798570031065272942592 else 5708992217023898938221613597140062130545885184))) else (if j.val < 301 then (if j.val < 300 then 11417984434047797876443227194280124261091770368 else 22835968868095595752886454388560248522183540736) else (if j.val < 302 then 45671937736191191505772908777120497044367081472 else (if j.val < 303 then 91343875472382383011545817554240994088734162944 else 182687750944764766023091635108481988177468325888)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then 365375501889529532046183270216963976354936651776 else 730751003779059064092366540433927952709873303552) else (if j.val < 307 then 1461502007558118128184733080867855905419746607104 else (if j.val < 308 then 2923004015116236256369466161735711810839493214208 else 5846008030232472512738932323471423621678986428416))) else (if j.val < 312 then (if j.val < 310 then 11692016060464945025477864646942847243357972856832 else (if j.val < 311 then 23384032120929890050955729293885694486715945713664 else 46768064241859780101911458587771388973431891427328)) else (if j.val < 313 then 93536128483719560203822917175542777946863782854656 else (if j.val < 314 then 187072256967439120407645834351085555893727565709312 else 94778167093755148370869615772589603195715584))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 189556334187510296741739231545179206391431168 else 379112668375020593483478463090358412782862336) else (if j.val < 318 then 758225336750041186966956926180716825565724672 else (if j.val < 319 then 1516450673500082373933913852361433651131449344 else 3032901347000164747867827704722867302262898688))) else (if j.val < 322 then (if j.val < 321 then 6065802694000329495735655409445734604525797376 else 12131605388000658991471310818891469209051594752) else (if j.val < 323 then 24263210776001317982942621637782938418103189504 else (if j.val < 324 then 48526421552002635965885243275565876836206379008 else 97052843104005271931770486551131753672412758016)))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then 194105686208010543863540973102263507344825516032 else 388211372416021087727081946204527014689651032064) else (if j.val < 328 then 776422744832042175454163892409054029379302064128 else (if j.val < 329 then 1552845489664084350908327784818108058758604128256 else 3105690979328168701816655569636216117517208256512))) else (if j.val < 333 then (if j.val < 331 then 6211381958656337403633311139272432235034416513024 else (if j.val < 332 then 12422763917312674807266622278544864470068833026048 else 24845527834625349614533244557089728940137666052096)) else (if j.val < 334 then 49691055669250699229066489114179457880275332104192 else (if j.val < 335 then 99382111338501398458132978228358915760550664208384 else 198764222677002796916265956456717831521101328416768)))))))))
def xrow (i : Fin 168) : BitVec 336 := BitVec.ofNat 336 (if i.val < 84 then (if i.val < 42 then (if i.val < 21 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 1725436586697640953219144091233345863135214253993879983023386932543491 else 3450873173395281906438288182466691726270428507987759966046773865086982) else (if i.val < 3 then 6901746346790563812876576364933383452540857015975519932093547730173964 else (if i.val < 4 then 13803492693581127625753152729866766905081714031951039864187095460347928 else 27606985387162255251506305459733533810163428063902079728374190920695856))) else (if i.val < 7 then (if i.val < 6 then 55213970774324510503012610919467067620326856127804159456748381841391712 else 110427941548649021006025221838934135240653712255608318913496763682783424) else (if i.val < 8 then 220855883097298042012050443677868270481307424511216637826993527365566848 else (if i.val < 9 then 441711766194596084024100887355736540962614849022433275653987054731133696 else 883423532389192168048201774711473081925229698044866551307974109462267392)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 1766847064778384336096403549422946163850459396089733102615948218924534784 else 3533694129556768672192807098845892327700918792179466205231896437849069568) else (if i.val < 13 then 7067388259113537344385614197691784655401837584358932410463792875698139136 else (if i.val < 14 then 14134776518227074688771228395383569310803675168717864820927585751396278272 else 28269553036454149377542456790767138621607350337435729641855171502792556544))) else (if i.val < 18 then (if i.val < 16 then 56539106072908298755084913581534277243214700674871459283710343005585113088 else (if i.val < 17 then 113078212145816597510169827163068554486429401349742918567420686011170226176 else 226156424291633195020339654326137108972858802699485837134841372022340452352)) else (if i.val < 19 then 452312848583266390040679308652274217945717605398971674269682744044680904704 else (if i.val < 20 then 904625697166532780081358617304548435891435210797943348539365488089361809408 else 1809251394333065560162717234609096871782870421595886697078730976178723618816))))) else (if i.val < 31 then (if i.val < 26 then (if i.val < 23 then (if i.val < 22 then 3618502788666131120325434469218193743565740843191773394157461952357447237632 else 26677682749537812403013254704924328711217277936139054874624) else (if i.val < 24 then 53355365499075624806026509409848657422434555872278109749248 else (if i.val < 25 then 106710730998151249612053018819697314844869111744556219498496 else 213421461996302499224106037639394629689738223489112438996992))) else (if i.val < 28 then (if i.val < 27 then 426842923992604998448212075278789259379476446978224877993984 else 853685847985209996896424150557578518758952893956449755987968) else (if i.val < 29 then 1707371695970419993792848301115157037517905787912899511975936 else (if i.val < 30 then 3414743391940839987585696602230314075035811575825799023951872 else 6829486783881679975171393204460628150071623151651598047903744)))) else (if i.val < 36 then (if i.val < 33 then (if i.val < 32 then 13658973567763359950342786408921256300143246303303196095807488 else 27317947135526719900685572817842512600286492606606392191614976) else (if i.val < 34 then 54635894271053439801371145635685025200572985213212784383229952 else (if i.val < 35 then 109271788542106879602742291271370050401145970426425568766459904 else 218543577084213759205484582542740100802291940852851137532919808))) else (if i.val < 39 then (if i.val < 37 then 437087154168427518410969165085480201604583881705702275065839616 else (if i.val < 38 then 874174308336855036821938330170960403209167763411404550131679232 else 1748348616673710073643876660341920806418335526822809100263358464)) else (if i.val < 40 then 3496697233347420147287753320683841612836671053645618200526716928 else (if i.val < 41 then 6993394466694840294575506641367683225673342107291236401053433856 else 13986788933389680589151013282735366451346684214582472802106867712)))))) else (if i.val < 63 then (if i.val < 52 then (if i.val < 47 then (if i.val < 44 then (if i.val < 43 then 27973577866779361178302026565470732902693368429164945604213735424 else 55947155733558722356604053130941465805386736858329891208427470848) else (if i.val < 45 then 111894311467117444713208106261882931610773473716659782416854941696 else (if i.val < 46 then 223788622934234889426416212523765863221546947433319564833709883392 else 447577245868469778852832425047531726443093894866639129667419766784))) else (if i.val < 49 then (if i.val < 48 then 895154491736939557705664850095063452886187789733278259334839533568 else 1790308983473879115411329700190126905772375579466556518669679067136) else (if i.val < 50 then 3580617966947758230822659400380253811544751158933113037339358134272 else (if i.val < 51 then 7161235933895516461645318800760507623089502317866226074678716268544 else 14322471867791032923290637601521015246179004635732452149357432537088)))) else (if i.val < 57 then (if i.val < 54 then (if i.val < 53 then 28644943735582065846581275203042030492358009271464904298714865074176 else 57289887471164131693162550406084060984716018542929808597429730148352) else (if i.val < 55 then 114579774942328263386325100812168121969432037085859617194859460296704 else (if i.val < 56 then 229159549884656526772650201624336243938864074171719234389718920593408 else 458319099769313053545300403248672487877728148343438468779437841186816))) else (if i.val < 60 then (if i.val < 58 then 916638199538626107090600806497344975755456296686876937558875682373632 else (if i.val < 59 then 1833276399077252214181201612994689951510912593373753875117751364747264 else 3666552798154504428362403225989379903021825186747507750235502729494528)) else (if i.val < 61 then 7333105596309008856724806451978759806043650373495015500471005458989056 else (if i.val < 62 then 14666211192618017713449612903957519612087300746990031000942010917978112 else 29332422385236035426899225807915039224174601493980062001884021835956224))))) else (if i.val < 73 then (if i.val < 68 then (if i.val < 65 then (if i.val < 64 then 58664844770472070853798451615830078448349202987960124003768043671912448 else 117329689540944141707596903231660156896698405975920248007536087343824896) else (if i.val < 66 then 234659379081888283415193806463320313793396811951840496015072174687649792 else (if i.val < 67 then 469318758163776566830387612926640627586793623903680992030144349375299584 else 938637516327553133660775225853281255173587247807361984060288698750599168))) else (if i.val < 70 then (if i.val < 69 then 1877275032655106267321550451706562510347174495614723968120577397501198336 else 3754550065310212534643100903413125020694348991229447936241154795002396672) else (if i.val < 71 then 7509100130620425069286201806826250041388697982458895872482309590004793344 else (if i.val < 72 then 15018200261240850138572403613652500082777395964917791744964619180009586688 else 30036400522481700277144807227305000165554791929835583489929238360019173376)))) else (if i.val < 78 then (if i.val < 75 then (if i.val < 74 then 60072801044963400554289614454610000331109583859671166979858476720038346752 else 120145602089926801108579228909220000662219167719342333959716953440076693504) else (if i.val < 76 then 240291204179853602217158457818440001324438335438684667919433906880153387008 else (if i.val < 77 then 480582408359707204434316915636880002648876670877369335838867813760306774016 else 961164816719414408868633831273760005297753341754738671677735627520613548032))) else (if i.val < 81 then (if i.val < 79 then 1922329633438828817737267662547520010595506683509477343355471255041227096064 else (if i.val < 80 then 3844659266877657635474534950950620864479866306875656854155603312230518489088 else 452312956423053056975883713002666644841505632292095631213560655885197377536)) else (if i.val < 82 then 904625912846106113951767426005333289683011264584191262427121311770394755072 else (if i.val < 83 then 1809251825692212227903534852010666579366022529168382524854242623540789510144 else 3618503651384424455807069704021333158732045058336745706895371413014783721473))))))) else (if i.val < 126 then (if i.val < 105 then (if i.val < 94 then (if i.val < 89 then (if i.val < 86 then (if i.val < 85 then 33374797436264220160451308973547709428211429733553601624521883829465340535685533104716868747296 else 66749594872528440320902617947095418856422859467107203249043767658930681071371066209433737494592) else (if i.val < 87 then 133499189745056880641805235894190837712845718934214406498087535317861362142742132418867474989184 else (if i.val < 88 then 266998379490113761283610471788381675425691437868428812996175070635722724285484264837734949978368 else 533996758980227522567220943576763350851382875736857625992350141271445448570968529675469899956736))) else (if i.val < 91 then (if i.val < 90 then 1067993517960455045134441887153526701702765751473715251984700282542890897141937059350939799913472 else 2135987035920910090268883774307053403405531502947430503969400565085781794283874118701879599826944) else (if i.val < 92 then 4271974071841820180537767548614106806811063005894861007938801130171563588567748237403759199653888 else (if i.val < 93 then 8543948143683640361075535097228213613622126011789722015877602260343127177135496474807518399307776 else 17087896287367280722151070194456427227244252023579444031755204520686254354270992949615036798615552)))) else (if i.val < 99 then (if i.val < 96 then (if i.val < 95 then 34175792574734561444302140388912854454488504047158888063510409041372508708541985899230073597231104 else 68351585149469122888604280777825708908977008094317776127020818082745017417083971798460147194462208) else (if i.val < 97 then 136703170298938245777208561555651417817954016188635552254041636165490034834167943596920294388924416 else (if i.val < 98 then 273406340597876491554417123111302835635908032377271104508083272330980069668335887193840588777848832 else 546812681195752983108834246222605671271816064754542209016166544661960139336671774387681177555697664))) else (if i.val < 102 then (if i.val < 100 then 1093625362391505966217668492445211342543632129509084418032333089323920278673343548775362355111395328 else (if i.val < 101 then 2187250724783011932435336984890422685087264259018168836064666178647840557346687097550724710222790656 else 4374501449566023864870673969780845370174528518036337672129332357295681114693374195101449420445581312)) else (if i.val < 103 then 8749002899132047729741347939561690740349057036072675344258664714591362229386748390202898840891162624 else (if i.val < 104 then 17498005798264095459482695879123381480698114072145350688517329429182724458773496780405797681782325248 else 34996011596528190918965391758246762961396228144290701377034658858365448917546993560811595363564650496))))) else (if i.val < 115 then (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then 69992023193056381837930783516493525922792456288581402754069317716730897835093987121623190727129300992 else 516021431734464861795244282973183772619883557452598845323963167623040538619353759744) else (if i.val < 108 then 1032042863468929723590488565946367545239767114905197690647926335246081077238707519488 else (if i.val < 109 then 2064085726937859447180977131892735090479534229810395381295852670492162154477415038976 else 4128171453875718894361954263785470180959068459620790762591705340984324308954830077952))) else (if i.val < 112 then (if i.val < 111 then 8256342907751437788723908527570940361918136919241581525183410681968648617909660155904 else 16512685815502875577447817055141880723836273838483163050366821363937297235819320311808) else (if i.val < 113 then 33025371631005751154895634110283761447672547676966326100733642727874594471638640623616 else (if i.val < 114 then 66050743262011502309791268220567522895345095353932652201467285455749188943277281247232 else 132101486524023004619582536441135045790690190707865304402934570911498377886554562494464)))) else (if i.val < 120 then (if i.val < 117 then (if i.val < 116 then 264202973048046009239165072882270091581380381415730608805869141822996755773109124988928 else 528405946096092018478330145764540183162760762831461217611738283645993511546218249977856) else (if i.val < 118 then 1056811892192184036956660291529080366325521525662922435223476567291987023092436499955712 else (if i.val < 119 then 2113623784384368073913320583058160732651043051325844870446953134583974046184872999911424 else 4227247568768736147826641166116321465302086102651689740893906269167948092369745999822848))) else (if i.val < 123 then (if i.val < 121 then 8454495137537472295653282332232642930604172205303379481787812538335896184739491999645696 else (if i.val < 122 then 16908990275074944591306564664465285861208344410606758963575625076671792369478983999291392 else 33817980550149889182613129328930571722416688821213517927151250153343584738957967998582784)) else (if i.val < 124 then 67635961100299778365226258657861143444833377642427035854302500306687169477915935997165568 else (if i.val < 125 then 135271922200599556730452517315722286889666755284854071708605000613374338955831871994331136 else 270543844401199113460905034631444573779333510569708143417210001226748677911663743988662272)))))) else (if i.val < 147 then (if i.val < 136 then (if i.val < 131 then (if i.val < 128 then (if i.val < 127 then 541087688802398226921810069262889147558667021139416286834420002453497355823327487977324544 else 1082175377604796453843620138525778295117334042278832573668840004906994711646654975954649088) else (if i.val < 129 then 2164350755209592907687240277051556590234668084557665147337680009813989423293309951909298176 else (if i.val < 130 then 4328701510419185815374480554103113180469336169115330294675360019627978846586619903818596352 else 8657403020838371630748961108206226360938672338230660589350720039255957693173239807637192704))) else (if i.val < 133 then (if i.val < 132 then 17314806041676743261497922216412452721877344676461321178701440078511915386346479615274385408 else 34629612083353486522995844432824905443754689352922642357402880157023830772692959230548770816) else (if i.val < 134 then 69259224166706973045991688865649810887509378705845284714805760314047661545385918461097541632 else (if i.val < 135 then 138518448333413946091983377731299621775018757411690569429611520628095323090771836922195083264 else 277036896666827892183966755462599243550037514823381138859223041256190646181543673844390166528)))) else (if i.val < 141 then (if i.val < 138 then (if i.val < 137 then 554073793333655784367933510925198487100075029646762277718446082512381292363087347688780333056 else 1108147586667311568735867021850396974200150059293524555436892165024762584726174695377560666112) else (if i.val < 139 then 2216295173334623137471734043700793948400300118587049110873784330049525169452349390755121332224 else (if i.val < 140 then 4432590346669246274943468087401587896800600237174098221747568660099050338904698781510242664448 else 8865180693338492549886936174803175793601200474348196443495137320198100677809397563020485328896))) else (if i.val < 144 then (if i.val < 142 then 17730361386676985099773872349606351587202400948696392886990274640396201355618795126040970657792 else (if i.val < 143 then 35460722773353970199547744699212703174404801897392785773980549280792402711237590252081941315584 else 70921445546707940399095489398425406348809603794785571547961098561584805422475180504163882631168)) else (if i.val < 145 then 141842891093415880798190978796850812697619207589571143095922197123169610844950361008327765262336 else (if i.val < 146 then 283685782186831761596381957593701625395238415179142286191844394246339221689900722016655530524672 else 567371564373663523192763915187403250790476830358284572383688788492678443379801444033311061049344))))) else (if i.val < 157 then (if i.val < 152 then (if i.val < 149 then (if i.val < 148 then 1134743128747327046385527830374806501580953660716569144767377576985356886759602888066622122098688 else 2269486257494654092771055660749613003161907321433138289534755153970713773519205776133244244197376) else (if i.val < 150 then 4538972514989308185542111321499226006323814642866276579069510307941427547038411552266488488394752 else (if i.val < 151 then 9077945029978616371084222642998452012647629285732553158139020615882855094076823104532976976789504 else 18155890059957232742168445285996904025295258571465106316278041231765710188153646209065953953579008))) else (if i.val < 154 then (if i.val < 153 then 36311780119914465484336890571993808050590517142930212632556082463531420376307292418131907907158016 else 72623560239828930968673781143987616101181034285860425265112164927062840752614584836263815814316032) else (if i.val < 155 then 145247120479657861937347562287975232202362068571720850530224329854125681505229169672527631628632064 else (if i.val < 156 then 290494240959315723874695124575950464404724137143441701060448659708251363010458339345055263257264128 else 580988481918631447749390249151900928809448274286883402120897319416502726020916678690110526514528256)))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then 1161976963837262895498780498303801857618896548573766804241794638833005452041833357380221053029056512 else 2323953927674525790997560996607603715237793097147533608483589277666010904083666714760442106058113024) else (if i.val < 160 then 4647907855349051581995121993215207430475586194295067216967178555332021808167333429520884212116226048 else (if i.val < 161 then 9295815710698103163990243986430414860951172388590134433934357110664043616334666859041768424232452096 else 18591631421396206327980487972860829721902344777180268867868714221328087232669333718083536848464904192))) else (if i.val < 165 then (if i.val < 163 then 37183262842792412655960975945721659443804689554360537735737428442656174465338667436167073696929808384 else (if i.val < 164 then 74366525685584825311921951891443318887609379108721075471474856885312348930657992059220313327064317953 else 8749004985056887464003768484364447724878128613463118054694635789761747515091177498234783819223793666)) else (if i.val < 166 then 17498009970113774928007536968728895449756257226926236109389271579523495030182354996469567638447587332 else (if i.val < 167 then 34996019940227549856015073937457790899512514453852472218778543159046990060364709992939135276895174664 else 69992039880455099712030147874915581799025028907704570293137929606946919977431587430539072701854646288))))))))
def xH : Matrix (Fin 168) (Fin 336) (ZMod 2) := fun i j => entry (xmask j) i
def zmask (j : Fin 336) : BitVec 168 := BitVec.ofNat 168 (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4611686018427387921 else 9223372036854775842) else (if j.val < 3 then 18446744073709551684 else (if j.val < 4 then 36893488147419103368 else 73786976294838206736))) else (if j.val < 7 then (if j.val < 6 then 147573952589676413472 else 295147905179352826944) else (if j.val < 8 then 590295810358705653888 else (if j.val < 9 then 1180591620717411307776 else 2361183241434822615552)))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then 4722366482869645231104 else 9444732965739290462208) else (if j.val < 13 then 18889465931478580924416 else (if j.val < 14 then 37778931862957161848832 else 75557863725914323697664))) else (if j.val < 18 then (if j.val < 16 then 151115727451828647395328 else (if j.val < 17 then 302231454903657294790656 else 604462909807314589581312)) else (if j.val < 19 then 1208925819614629179162624 else (if j.val < 20 then 2417851639229258358325248 else 4835703278458516716650496))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then 9671406556917033433300992 else 71303169) else (if j.val < 24 then 142606338 else (if j.val < 25 then 285212676 else 570425352))) else (if j.val < 28 then (if j.val < 27 then 1140850704 else 2281701408) else (if j.val < 29 then 4563402816 else (if j.val < 30 then 9126805632 else 18253611264)))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then 36507222528 else 73014445056) else (if j.val < 34 then 146028890112 else (if j.val < 35 then 292057780224 else 584115560448))) else (if j.val < 39 then (if j.val < 37 then 1168231120896 else (if j.val < 38 then 2336462241792 else 4672924483584)) else (if j.val < 40 then 9345848967168 else (if j.val < 41 then 18691697934336 else 37383395868672)))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then 74766791737344 else 149533583474688) else (if j.val < 45 then 299067166949376 else (if j.val < 46 then 598134333898752 else 1196268667797504))) else (if j.val < 49 then (if j.val < 48 then 2392537335595008 else 4785074671190016) else (if j.val < 50 then 9570149342380032 else (if j.val < 51 then 19140298684760064 else 38280597369520128)))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then 76561194739040256 else 153122389478080512) else (if j.val < 55 then 306244778956161024 else (if j.val < 56 then 612489557912322048 else 1224979115824644096))) else (if j.val < 60 then (if j.val < 58 then 2449958231649288192 else (if j.val < 59 then 4899916463298576384 else 9799832926597152768)) else (if j.val < 61 then 19599665853194305536 else (if j.val < 62 then 39199331706388611072 else 78398663412777222144))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then 156797326825554444288 else 313594653651108888576) else (if j.val < 66 then 627189307302217777152 else (if j.val < 67 then 1254378614604435554304 else 2508757229208871108608))) else (if j.val < 70 then (if j.val < 69 then 5017514458417742217216 else 10035028916835484434432) else (if j.val < 71 then 20070057833670968868864 else (if j.val < 72 then 40140115667341937737728 else 80280231334683875475456)))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then 160560462669367750950912 else 321120925338735501901824) else (if j.val < 76 then 642241850677471003803648 else (if j.val < 77 then 1284483701354942007607296 else 2568967402709884015214592))) else (if j.val < 81 then (if j.val < 79 then 5137934805419768030429184 else (if j.val < 80 then 10275869610839536060858368 else 1208926107845005326417921)) else (if j.val < 82 then 2417852215690010652835842 else (if j.val < 83 then 4835704431380021305671684 else 9671408862760042611343368))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then 89202980794122492894970696025772581544001536 else 178405961588244985789941392051545163088003072) else (if j.val < 87 then 356811923176489971579882784103090326176006144 else (if j.val < 88 then 713623846352979943159765568206180652352012288 else 1427247692705959886319531136412361304704024576))) else (if j.val < 91 then (if j.val < 90 then 2854495385411919772639062272824722609408049152 else 5708990770823839545278124545649445218816098304) else (if j.val < 92 then 11417981541647679090556249091298890437632196608 else (if j.val < 93 then 22835963083295358181112498182597780875264393216 else 45671926166590716362224996365195561750528786432)))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then 91343852333181432724449992730391123501057572864 else 182687704666362865448899985460782247002115145728) else (if j.val < 97 then 365375409332725730897799970921564494004230291456 else (if j.val < 98 then 730750818665451461795599941843128988008460582912 else 1461501637330902923591199883686257976016921165824))) else (if j.val < 102 then (if j.val < 100 then 2923003274661805847182399767372515952033842331648 else (if j.val < 101 then 5846006549323611694364799534745031904067684663296 else 11692013098647223388729599069490063808135369326592)) else (if j.val < 103 then 23384026197294446777459198138980127616270738653184 else (if j.val < 104 then 46768052394588893554918396277960255232541477306368 else 93536104789177787109836792555920510465082954612736))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then 187072209578355574219673585111841020930165909225472 else 1379203872391126702662479882747904) else (if j.val < 108 then 2758407744782253405324959765495808 else (if j.val < 109 then 5516815489564506810649919530991616 else 11033630979129013621299839061983232))) else (if j.val < 112 then (if j.val < 111 then 22067261958258027242599678123966464 else 44134523916516054485199356247932928) else (if j.val < 113 then 88269047833032108970398712495865856 else (if j.val < 114 then 176538095666064217940797424991731712 else 353076191332128435881594849983463424)))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then 706152382664256871763189699966926848 else 1412304765328513743526379399933853696) else (if j.val < 118 then 2824609530657027487052758799867707392 else (if j.val < 119 then 5649219061314054974105517599735414784 else 11298438122628109948211035199470829568))) else (if j.val < 123 then (if j.val < 121 then 22596876245256219896422070398941659136 else (if j.val < 122 then 45193752490512439792844140797883318272 else 90387504981024879585688281595766636544)) else (if j.val < 124 then 180775009962049759171376563191533273088 else (if j.val < 125 then 361550019924099518342753126383066546176 else 723100039848199036685506252766133092352)))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then 1446200079696398073371012505532266184704 else 2892400159392796146742025011064532369408) else (if j.val < 129 then 5784800318785592293484050022129064738816 else (if j.val < 130 then 11569600637571184586968100044258129477632 else 23139201275142369173936200088516258955264))) else (if j.val < 133 then (if j.val < 132 then 46278402550284738347872400177032517910528 else 92556805100569476695744800354065035821056) else (if j.val < 134 then 185113610201138953391489600708130071642112 else (if j.val < 135 then 370227220402277906782979201416260143284224 else 740454440804555813565958402832520286568448)))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then 1480908881609111627131916805665040573136896 else 2961817763218223254263833611330081146273792) else (if j.val < 139 then 5923635526436446508527667222660162292547584 else (if j.val < 140 then 11847271052872893017055334445320324585095168 else 23694542105745786034110668890640649170190336))) else (if j.val < 144 then (if j.val < 142 then 47389084211491572068221337781281298340380672 else (if j.val < 143 then 94778168422983144136442675562562596680761344 else 189556336845966288272885351125125193361522688)) else (if j.val < 145 then 379112673691932576545770702250250386723045376 else (if j.val < 146 then 758225347383865153091541404500500773446090752 else 1516450694767730306183082809001001546892181504))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then 3032901389535460612366165618002003093784363008 else 6065802779070921224732331236004006187568726016) else (if j.val < 150 then 12131605558141842449464662472008012375137452032 else (if j.val < 151 then 24263211116283684898929324944016024750274904064 else 48526422232567369797858649888032049500549808128))) else (if j.val < 154 then (if j.val < 153 then 97052844465134739595717299776064099001099616256 else 194105688930269479191434599552128198002199232512) else (if j.val < 155 then 388211377860538958382869199104256396004398465024 else (if j.val < 156 then 776422755721077916765738398208512792008796930048 else 1552845511442155833531476796417025584017593860096)))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 3105691022884311667062953592834051168035187720192 else 6211382045768623334125907185668102336070375440384) else (if j.val < 160 then 12422764091537246668251814371336204672140750880768 else (if j.val < 161 then 24845528183074493336503628742672409344281501761536 else 49691056366148986673007257485344818688563003523072))) else (if j.val < 165 then (if j.val < 163 then 99382112732297973346014514970689637377126007046144 else (if j.val < 164 then 198764225464595946692029029941379274754252014092288 else 23384031772480746323914762050203210310652092481536)) else (if j.val < 166 then 46768063544961492647829524100406420621304184963072 else (if j.val < 167 then 93536127089922985295659048200812841242608369926144 else 187072254179845970591318096401625682485216739852288)))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then 618970019642690137449562115 else 1237940039285380274899124230) else (if j.val < 171 then 2475880078570760549798248460 else (if j.val < 172 then 4951760157141521099596496920 else 9903520314283042199192993840))) else (if j.val < 175 then (if j.val < 174 then 19807040628566084398385987680 else 39614081257132168796771975360) else (if j.val < 176 then 79228162514264337593543950720 else (if j.val < 177 then 158456325028528675187087901440 else 316912650057057350374175802880)))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then 633825300114114700748351605760 else 1267650600228229401496703211520) else (if j.val < 181 then 2535301200456458802993406423040 else (if j.val < 182 then 5070602400912917605986812846080 else 10141204801825835211973625692160))) else (if j.val < 186 then (if j.val < 184 then 20282409603651670423947251384320 else (if j.val < 185 then 40564819207303340847894502768640 else 81129638414606681695789005537280)) else (if j.val < 187 then 162259276829213363391578011074560 else (if j.val < 188 then 324518553658426726783156022149120 else 649037107316853453566312044298240))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then 1298074214633706907132624088596480 else 2596148429267413814265248177192960) else (if j.val < 192 then 5192296858534827628530496354385920 else (if j.val < 193 then 10384593717069655257060992708771840 else 20769187434139310514121985417543680))) else (if j.val < 196 then (if j.val < 195 then 41538374868278621028243970835087360 else 83076749736557242056487941670174720) else (if j.val < 197 then 166153499473114484112975883340349440 else (if j.val < 198 then 332306998946228968225951766680698880 else 664613997892457936451903533361397760)))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then 1329227995784915872903807066722795520 else 2658455991569831745807614133445591040) else (if j.val < 202 then 5316911983139663491615228266891182080 else (if j.val < 203 then 10633823966279326983230456533782364160 else 21267647932558653966460913067564728320))) else (if j.val < 207 then (if j.val < 205 then 42535295865117307932921826135129456640 else (if j.val < 206 then 85070591730234615865843652270258913280 else 170141183460469231731687304540517826560)) else (if j.val < 208 then 340282366920938463463374609081035653120 else (if j.val < 209 then 680564733841876926926749218162071306240 else 1361129467683753853853498436324142612480)))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then 2722258935367507707706996872648285224960 else 5444517870735015415413993745296570449920) else (if j.val < 213 then 10889035741470030830827987490593140899840 else (if j.val < 214 then 21778071482940061661655974981186281799680 else 43556142965880123323311949962372563599360))) else (if j.val < 217 then (if j.val < 216 then 87112285931760246646623899924745127198720 else 174224571863520493293247799849490254397440) else (if j.val < 218 then 348449143727040986586495599698980508794880 else (if j.val < 219 then 696898287454081973172991199397961017589760 else 1393796574908163946345982398795922035179520)))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then 2787593149816327892691964797591844070359040 else 5575186299632655785383929595183688140718080) else (if j.val < 223 then 11150372599265311570767859190367376281436160 else (if j.val < 224 then 22300745198530623141535718380734752562872320 else 44601490397061246283071436761469505125744640))) else (if j.val < 228 then (if j.val < 226 then 89202980794122492566142873522939010251489280 else (if j.val < 227 then 178405961588244985132285747045878020502978560 else 356811923176489970264571494091756041005957120)) else (if j.val < 229 then 713623846352979940529142988183512082011914240 else (if j.val < 230 then 1427247692705959881058285976367024164023828480 else 2854495385411919762116571952734048328047656960))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then 5708990770823839524233143905468096656095313920 else 11417981541647679048466287810936193312190627840) else (if j.val < 234 then 22835963083295358096932575621872386624381255680 else (if j.val < 235 then 45671926166590716193865151243744773248762511360 else 91343852333181432387730302487489546497525022720))) else (if j.val < 238 then (if j.val < 237 then 182687704666362864775460604974979092995050045440 else 365375409332725729550921209949958185990100090880) else (if j.val < 239 then 730750818665451459101842419899916371980200181760 else (if j.val < 240 then 1461501637330902918203684839799832743960400363520 else 2923003274661805836407369679599665487920800727040)))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then 5846006549323611672814739359199330975841601454080 else 11692013098647223345629478718398661951683202908160) else (if j.val < 244 then 23384026197294446691258957436797323903366405816320 else (if j.val < 245 then 46768052394588893382517914873594647806732811632640 else 93536104789177786765035829747189295613465623265280))) else (if j.val < 249 then (if j.val < 247 then 187072209578355573530071659494378591226931246530560 else (if j.val < 248 then 21156201843256010557358080 else 42312403686512021114716160)) else (if j.val < 250 then 84624807373024042229432320 else (if j.val < 251 then 169249614746048084458864640 else 319156416378262102122430465))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then 58028439341502200385896480 else 116056878683004400771792960) else (if j.val < 255 then 232113757366008801543585920 else (if j.val < 256 then 464227514732017603087171840 else 928455029464035206174343680))) else (if j.val < 259 then (if j.val < 258 then 1856910058928070412348687360 else 3713820117856140824697374720) else (if j.val < 260 then 7427640235712281649394749440 else (if j.val < 261 then 14855280471424563298789498880 else 29710560942849126597578997760)))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then 59421121885698253195157995520 else 118842243771396506390315991040) else (if j.val < 265 then 237684487542793012780631982080 else (if j.val < 266 then 475368975085586025561263964160 else 950737950171172051122527928320))) else (if j.val < 270 then (if j.val < 268 then 1901475900342344102245055856640 else (if j.val < 269 then 3802951800684688204490111713280 else 7605903601369376408980223426560)) else (if j.val < 271 then 15211807202738752817960446853120 else (if j.val < 272 then 30423614405477505635920893706240 else 60847228810955011271841787412480))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then 121694457621910022543683574824960 else 243388915243820045087367149649920) else (if j.val < 276 then 486777830487640090174734299299840 else (if j.val < 277 then 973555660975280180349468598599680 else 1947111321950560360698937197199360))) else (if j.val < 280 then (if j.val < 279 then 3894222643901120721397874394398720 else 7788445287802241442795748788797440) else (if j.val < 281 then 15576890575604482885591497577594880 else (if j.val < 282 then 31153781151208965771182995155189760 else 62307562302417931542365990310379520)))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then 124615124604835863084731980620759040 else 249230249209671726169463961241518080) else (if j.val < 286 then 498460498419343452338927922483036160 else (if j.val < 287 then 996920996838686904677855844966072320 else 1993841993677373809355711689932144640))) else (if j.val < 291 then (if j.val < 289 then 3987683987354747618711423379864289280 else (if j.val < 290 then 7975367974709495237422846759728578560 else 15950735949418990474845693519457157120)) else (if j.val < 292 then 31901471898837980949691387038914314240 else (if j.val < 293 then 63802943797675961899382774077828628480 else 127605887595351923798765548155657256960)))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then 255211775190703847597531096311314513920 else 510423550381407695195062192622629027840) else (if j.val < 297 then 1020847100762815390390124385245258055680 else (if j.val < 298 then 2041694201525630780780248770490516111360 else 4083388403051261561560497540981032222720))) else (if j.val < 301 then (if j.val < 300 then 8166776806102523123120995081962064445440 else 16333553612205046246241990163924128890880) else (if j.val < 302 then 32667107224410092492483980327848257781760 else (if j.val < 303 then 65334214448820184984967960655696515563520 else 130668428897640369969935921311393031127040)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then 261336857795280739939871842622786062254080 else 522673715590561479879743685245572124508160) else (if j.val < 307 then 1045347431181122959759487370491144249016320 else (if j.val < 308 then 2090694862362245919518974740982288498032640 else 4181389724724491839037949481964576996065280))) else (if j.val < 312 then (if j.val < 310 then 8362779449448983678075898963929153992130560 else (if j.val < 311 then 16725558898897967356151797927858307984261120 else 33451117797795934712303595855716615968522240)) else (if j.val < 313 then 66902235595591869424607191711433231937044480 else (if j.val < 314 then 133804471191183738849214383422866463874088960 else 267608942382367477698428766845732927748177920))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 535217884764734955396857533691465855496355840 else 1070435769529469910793715067382931710992711680) else (if j.val < 318 then 2140871539058939821587430134765863421985423360 else (if j.val < 319 then 4281743078117879643174860269531726843970846720 else 8563486156235759286349720539063453687941693440))) else (if j.val < 322 then (if j.val < 321 then 17126972312471518572699441078126907375883386880 else 34253944624943037145398882156253814751766773760) else (if j.val < 323 then 68507889249886074290797764312507629503533547520 else (if j.val < 324 then 137015778499772148581595528625015259007067095040 else 274031556999544297163191057250030518014134190080)))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then 548063113999088594326382114500061036028268380160 else 1096126227998177188652764229000122072056536760320) else (if j.val < 328 then 2192252455996354377305528458000244144113073520640 else (if j.val < 329 then 4384504911992708754611056916000488288226147041280 else 8769009823985417509222113832000976576452294082560))) else (if j.val < 333 then (if j.val < 331 then 17538019647970835018444227664001953152904588165120 else (if j.val < 332 then 35076039295941670036888435985190792471742381031425 else 70152078591883340073776871970381584943484762062850)) else (if j.val < 334 then 140304157183766680147553743940763169886969524125700 else (if j.val < 335 then 280608314367533360295107487881526339773939048251400 else 187072209578355573530071677930497340350026160799760)))))))))
def zH : Matrix (Fin 168) (Fin 336) (ZMod 2) := fun i j => entry (zmask j) i
end BB336KernelData

set_option maxHeartbeats 0
open Matrix BBCode
namespace BB336Symmetry

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
    have he := (BB336Cert.rowspace_reindex (HX A B) negG dualQ v)
    rw [HX_dual] at he
    exact hv.2 (he.mp h)
end BB336Symmetry

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336Cert BB336Bits
namespace BB336KernelData
def polyA : Poly 2 84 := {(0,0),(0,1),(1,5)}
def polyB : Poly 2 84 := {(0,0),(0,4),(0,62)}
def er : Fin 168 ≃ Grp 2 84 where
  toFun i := ((i.val / 84 : ℕ), (i.val % 84 : ℕ))
  invFun g := ⟨g.1.val * 84 + g.2.val, by
    have h1 := ZMod.val_lt g.1
    have h2 := ZMod.val_lt g.2
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eqb : Fin 336 ≃ Qubit 2 84 where
  toFun i := if h : i.val < 168 then Sum.inl (er ⟨i.val,h⟩)
    else Sum.inr (er ⟨i.val-168,by omega⟩)
  invFun q := match q with
    | Sum.inl g => ⟨(er.symm g).val, by have h := (er.symm g).isLt; omega⟩
    | Sum.inr g => ⟨168 + (er.symm g).val, by have h := (er.symm g).isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

namespace BB336Sparse

lemma col_three (a b c g : Grp 2 84) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 168) :
    circulant {a,b,c} (er i) g =
      entry (unit (er.symm (g-a)) ^^^ unit (er.symm (g-b)) ^^^ unit (er.symm (g-c))) i := by
  have eqg (t : Grp 2 84) : i = er.symm (g-t) ↔ g-er i = t := by
    rw [Equiv.eq_symm_apply]
    constructor <;> intro h <;> linear_combination -h
  simp only [entry_xor,unit_entry,eqg,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
  by_cases ha : g-er i = a
  · have hb : g-er i ≠ b := by simpa only [ha] using hab
    have hc : g-er i ≠ c := by simpa only [ha] using hac
    simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
  · by_cases hb : g-er i = b
    · have hc : g-er i ≠ c := by simpa only [hb] using hbc
      simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
    · by_cases hc : g-er i = c <;> simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]

def column (q : Qubit 2 84) : BitVec 168 :=
  match q with
  | Sum.inl g => unit (er.symm (g-(0,0))) ^^^ unit (er.symm (g-(0,1))) ^^^ unit (er.symm (g-(1,5)))
  | Sum.inr g => unit (er.symm (g-(0,0))) ^^^ unit (er.symm (g-(0,4))) ^^^ unit (er.symm (g-(0,62)))

lemma column_entry (i : Fin 168) (q : Qubit 2 84) :
    HX polyA polyB (er i) q = entry (column q) i := by
  cases q with
  | inl g => exact col_three (0,0) (0,1) (1,5) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three (0,0) (0,4) (0,62) g (by decide) (by decide) (by decide) i

lemma xcolumn_bits : ∀ j, xmask j = column (eqb j) := by decide +kernel
lemma xtable_sparse : (HX polyA polyB).submatrix er eqb = xH := by
  ext i j
  change HX polyA polyB (er i) (eqb j) = entry (xmask j) i
  rw [xcolumn_bits,column_entry]
end BB336Sparse

namespace BB336Sparse
lemma col_three_z (a b c g : Grp 2 84) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 168) :
    circulant {a,b,c} g (er i) =
      entry (unit (er.symm (g+a)) ^^^ unit (er.symm (g+b)) ^^^ unit (er.symm (g+c))) i := by
  have eqg (t : Grp 2 84) : i = er.symm (g+t) ↔ er i-g = t := by
    rw [Equiv.eq_symm_apply]
    constructor <;> intro h <;> linear_combination h
  simp only [entry_xor,unit_entry,eqg,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
  by_cases ha : er i-g = a
  · have hb : er i-g ≠ b := by simpa only [ha] using hab
    have hc : er i-g ≠ c := by simpa only [ha] using hac
    simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
  · by_cases hb : er i-g = b
    · have hc : er i-g ≠ c := by simpa only [hb] using hbc
      simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
    · by_cases hc : er i-g = c <;> simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]


def zcolumn (q : Qubit 2 84) : BitVec 168 :=
  match q with
  | Sum.inl g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,4))) ^^^ unit (er.symm (g+(0,62)))
  | Sum.inr g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,1))) ^^^ unit (er.symm (g+(1,5)))

lemma zcolumn_entry (i : Fin 168) (q : Qubit 2 84) :
    HZ polyA polyB (er i) q = entry (zcolumn q) i := by
  cases q with
  | inl g => exact col_three_z (0,0) (0,4) (0,62) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three_z (0,0) (0,1) (1,5) g (by decide) (by decide) (by decide) i

lemma zcolumn_bits : ∀ j, zmask j = zcolumn (eqb j) := by decide +kernel
lemma ztable_sparse : (HZ polyA polyB).submatrix er eqb = zH := by
  ext i j
  change HZ polyA polyB (er i) (eqb j) = entry (zmask j) i
  rw [zcolumn_bits,zcolumn_entry]
end BB336Sparse

lemma xtable : (HX polyA polyB).submatrix er eqb = xH := BB336Sparse.xtable_sparse
lemma ztable : (HZ polyA polyB).submatrix er eqb = zH := BB336Sparse.ztable_sparse
lemma xcolParity : ∀ j, ∑ i, xH i j = 1 := by
  intro j
  change ∑ i, entry (xmask j) i = 1
  rw [BB336Sparse.xcolumn_bits]
  cases hq : eqb j with
  | inl g => simp [BB336Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
  | inr g => simp [BB336Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
lemma indicator_three {α : Type} [DecidableEq α] (a b c x : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((if x = a then (1 : ZMod 2) else 0) + (if x = b then 1 else 0)) +
      (if x = c then 1 else 0) = if x = a ∨ x = b ∨ x = c then 1 else 0 := by
  by_cases ha : x = a
  · have hb : x ≠ b := by simpa only [ha] using hab
    have hc : x ≠ c := by simpa only [ha] using hac
    simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
  · by_cases hb : x = b
    · have hc : x ≠ c := by simpa only [hb] using hbc
      simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
    · by_cases hc : x = c <;> simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
def rowFormula (i : Fin 168) : BitVec 336 :=
  unit (eqb.symm (Sum.inl (er i+(0,0)))) ^^^
  unit (eqb.symm (Sum.inl (er i+(0,1)))) ^^^
  unit (eqb.symm (Sum.inl (er i+(1,5)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,0)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,4)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,62))))
lemma row_formula_bits : ∀ i, xrow i = rowFormula i := by decide +kernel
lemma row_formula_entry (i : Fin 168) (j : Fin 336) :
    entry (rowFormula i) j = HX polyA polyB (er i) (eqb j) := by
  cases hq : eqb j with
  | inl g =>
    have yes (t : Grp 2 84) : j = eqb.symm (Sum.inl (er i+t)) ↔ g-er i = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inl.injEq,sub_eq_iff_eq_add,add_comm]
    have no (t : Grp 2 84) : j ≠ eqb.symm (Sum.inr (er i+t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [rowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HX,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,1) (1,5) (g-er i) (by decide) (by decide) (by decide)
  | inr g =>
    have yes (t : Grp 2 84) : j = eqb.symm (Sum.inr (er i+t)) ↔ g-er i = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inr.injEq,sub_eq_iff_eq_add,add_comm]
    have no (t : Grp 2 84) : j ≠ eqb.symm (Sum.inl (er i+t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [rowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HX,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,4) (0,62) (g-er i) (by decide) (by decide) (by decide)
lemma xrow_entry (i : Fin 168) (j : Fin 336) : entry (xrow i) j = xH i j := by
  rw [row_formula_bits,row_formula_entry]
  exact congrFun (congrFun xtable i) j
end BB336KernelData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB336Cert
namespace BB336Search

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
end BB336Search

set_option maxHeartbeats 0
open BB336Search
namespace BB336Count
lemma ones_xor_add {r : ℕ} (s t : BitVec r) :
    ones (s ^^^ t) + 2 * ∑ i : Fin r, (if s.getLsbD i.val then (t.getLsbD i.val).toNat else 0) =
    ones s + ones t := by
  rw [ones_eq,ones_eq,ones_eq,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases s.getLsbD i.val <;> cases t.getLsbD i.val <;> decide

lemma update_eq {r : ℕ} (s t : BitVec r) (ps : List (Fin r)) (hn : ps.Nodup)
    (hp : ps.toFinset = Finset.univ.filter (fun i => s.getLsbD i.val))
    (h3 : ones s = 3) :
    ones t + 3 - 2 * (ps.map fun i => (t.getLsbD i.val).toNat).sum = ones (s ^^^ t) := by
  have he : (ps.map fun i => (t.getLsbD i.val).toNat).sum =
      ∑ i : Fin r, (if s.getLsbD i.val then (t.getLsbD i.val).toNat else 0) := by
    rw [← List.sum_toFinset _ hn,hp,Finset.sum_filter]
  have h := ones_xor_add s t
  rw [h3,← he] at h
  omega
end BB336Count

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336Cert BB336Bits BB336Search
namespace BB336KernelData
def zrow (i : Fin 168) : BitVec 336 := BitVec.ofNat 336 (if i.val < 84 then (if i.val < 42 then (if i.val < 21 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 4374501449566023848745008072738031396837445848380080538767818338653986942984762373769173149241311233 else 8749002899132047697490008908470485461412677723573972178960552559080992426751447649892377722643021826) else (if i.val < 3 then 17498005798264095394980017816940970922825355447147944357921105118161984853502895299784755445286043652 else (if i.val < 4 then 34996011596528190789960035633881941845650710894295888715842210236323969707005790599569510890572087304 else 69992023193056381579920071267763883691301421788591777431684420472647939413992238386025187714348875793))) else (if i.val < 7 then (if i.val < 6 then 7237005577332262213973204521975113762964432928481759670151844532593792909346 else 14474011154664524427946409043950227525928865856963519340303689065187585818692) else (if i.val < 8 then 28948022309329048855892818087900455051857731713927038680607378130375171637384 else (if i.val < 9 then 57896044618658097711785636175800910103715463427854077361214756260750343274768 else 115792089237316195423571272351601820207430926855708154722429512521500686549536)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 231584178474632390847142544703203640414861853711416309444859025043001373099072 else 463168356949264781694285089406407280829723707422832618889718050086002746198144) else (if i.val < 13 then 926336713898529563388570178812814561659447414845665237779436100172005492396288 else (if i.val < 14 then 1852673427797059126777140357625629123318894829691330475558872200344010984792576 else 3705346855594118253554280715251258246637789659382660951117744400688021969585152))) else (if i.val < 18 then (if i.val < 16 then 7410693711188236507108561430502516493275579318765321902235488801376043939170304 else (if i.val < 17 then 14821387422376473014217122861005032986551158637530643804470977602752087878340608 else 29642774844752946028434245722010065973102317275061287608941955205504175756681216)) else (if i.val < 19 then 59285549689505892056868491444020131946204634550122575217883910411008351513362432 else (if i.val < 20 then 118571099379011784113736982888040263892409269100245150435767820822016703026724864 else 237142198758023568227473965776080527784818538200490300871535641644033406053449728))))) else (if i.val < 31 then (if i.val < 26 then (if i.val < 23 then (if i.val < 22 then 474284397516047136454947931552161055569637076400980601743071283288066812106899456 else 948568795032094272909895863104322111139274152801961203486142566576133624213798912) else (if i.val < 24 then 1897137590064188545819791726208644222278548305603922406972285133152267248427597824 else (if i.val < 25 then 3794275180128377091639583452417288444557096611207844813944570266304534496855195648 else 7588550360256754183279166904834576889114193222415689627889140532609068993710391296))) else (if i.val < 28 then (if i.val < 27 then 15177100720513508366558333809669153778228386444831379255778281065218137987420782592 else 30354201441027016733116667619338307556456772889662758511556562130436275974841565184) else (if i.val < 29 then 60708402882054033466233335238676615112913545779325517023113124260872551949683130368 else (if i.val < 30 then 121416805764108066932466670477353230225827091558651034046226248521745103899366260736 else 242833611528216133864933340954706460451654183117302068092452497043490207798732521472)))) else (if i.val < 36 then (if i.val < 33 then (if i.val < 32 then 485667223056432267729866681909412920903308366234604136184904994086980415597465042944 else 971334446112864535459733363818825841806616732469208272369809988173960831194930085888) else (if i.val < 34 then 1942668892225729070919466727637651683613233464938416544739619976347921662389860171776 else (if i.val < 35 then 3885337784451458141838933455275303367226466929876833089479239952695843324779720343552 else 7770675568902916283677866910550606734452933859753666178958479905391686649559440687104))) else (if i.val < 39 then (if i.val < 37 then 15541351137805832567355733821101213468905867719507332357916959810783373299118881374208 else (if i.val < 38 then 31082702275611665134711467642202426937811735439014664715833919621566746598237762748416 else 62165404551223330269422935284404853875623470878029329431667839243133493196475525496832)) else (if i.val < 40 then 124330809102446660538845870568809707751246941756058658863335678486266986392951050993664 else (if i.val < 41 then 248661618204893321077691741137619415502493883512117317726671356972533972785902101987328 else 497323236409786642155383482275238831004987767024234635453342713945067945571804203974656)))))) else (if i.val < 63 then (if i.val < 52 then (if i.val < 47 then (if i.val < 44 then (if i.val < 43 then 994646472819573284310766964550477662009975534048469270906685427890135891143608407949312 else 1989292945639146568621533929100955324019951068096938541813370855780271782287216815898624) else (if i.val < 45 then 3978585891278293137243067858201910648039902136193877083626741711560543564574433631797248 else (if i.val < 46 then 7957171782556586274486135716403821296079804272387754167253483423121087129148867263594496 else 15914343565113172548972271432807642592159608544775508334506966846242174258297734527188992))) else (if i.val < 49 then (if i.val < 48 then 31828687130226345097944542865615285184319217089551016669013933692484348516595469054377984 else 63657374260452690195889085731230570368638434179102033338027867384968697033190938108755968) else (if i.val < 50 then 127314748520905380391778171462461140737276868358204066676055734769937394066381876217511936 else (if i.val < 51 then 254629497041810760783556342924922281474553736716408133352111469539874788132763752435023872 else 509258994083621521567112685849844562949107473432816266704222939079749576265527504870047744)))) else (if i.val < 57 then (if i.val < 54 then (if i.val < 53 then 1018517988167243043134225371699689125898214946865632533408445878159499152531055009740095488 else 2037035976334486086268450743399378251796429893731265066816891756318998305062110019480190976) else (if i.val < 55 then 4074071952668972172536901486798756503592859787462530133633783512637996610124220038960381952 else (if i.val < 56 then 8148143905337944345073802973597513007185719574925060267267567025275993220248440077920763904 else 16296287810675888690147605947195026014371439149850120534535134050551986440496880155841527808))) else (if i.val < 60 then (if i.val < 58 then 32592575621351777380295211894390052028742878299700241069070268101103972880993760311683055616 else (if i.val < 59 then 65185151242703554760590423788780104057485756599400482138140536202207945761987520623366111232 else 130370302485407109521180847577560208114971513198800964276281072404415891523975041246732222464)) else (if i.val < 61 then 260740604970814219042361695155120416229943026397601928552562144808831783047950082493464444928 else (if i.val < 62 then 521481209941628438084723390310240832459886052795203857105124289617663566095900164986928889856 else 1042962419883256876169446780620481664919772105590407714210248579235307789378686495907062480897))))) else (if i.val < 73 then (if i.val < 68 then (if i.val < 65 then (if i.val < 64 then 2085924839766513752338893561240963329839544211180815428420497158470615578757372991814124961794 else 4171849679533027504677787122481926659679088422361630856840994316941231157514745983628249923588) else (if i.val < 66 then 8343699359066055009355574244963853319358176844723261713681988633882462315029491967256499847176 else (if i.val < 67 then 16687398718132110018711148489927706638716353689446523427363977267764924630058983934512999694352 else 33374797436264220037422296979855413277432707378893046854727954535529849260117967869025999388704))) else (if i.val < 70 then (if i.val < 69 then 66749594872528440074844593959710826554865414757786093709455909071059698520235935738051998777408 else 133499189745056880149689187919421653109730829515572187418911818142119397040471871476103997554816) else (if i.val < 71 then 266998379490113760299378375838843306219461659031144374837823636284238794080943742952207995109632 else (if i.val < 72 then 533996758980227520598756751677686612438923318062288749675647272568477588161887485904415990219264 else 1067993517960455041197513503355373224877846636124577499351294545136955176323774971808831980438528)))) else (if i.val < 78 then (if i.val < 75 then (if i.val < 74 then 2135987035920910082395027006710746449755693272249154998702589090273910352647549943617663960877056 else 4271974071841820164790054013421492899511386544498309997405178180547820705295099887235327921754112) else (if i.val < 76 then 8543948143683640329580108026842985799022773088996619994810356361095641410590199774470655843508224 else (if i.val < 77 then 17087896287367280659160216053685971598045546177993239989620712722191282821180399548941311687016448 else 34175792574734561318320432107371943196091092355986479979241425444382565642360799097882623374032896))) else (if i.val < 81 then (if i.val < 79 then 68351585149469122636640864214743886392182184711972959958482850888765131284721598195765246748065792 else (if i.val < 80 then 136703170298938245273281728429487772784364369423945919916965701777530262569443196391530493496131584 else 273406340597876490546563456858975545568728738847891839833931403555060525138886392783060986992263168)) else (if i.val < 82 then 546812681195752981093126913717951091137457477695783679667862807110121050277772785566121973984526336 else (if i.val < 83 then 1093625362391505962186253827435902182274914955391567359335725614220242100555545571132243947969052672 else 2187250724783011924372507654871804364549829910783134718671451228440484201111091142264487895938105344))))))) else (if i.val < 126 then (if i.val < 105 then (if i.val < 94 then (if i.val < 89 then (if i.val < 86 then (if i.val < 85 then 69992023193056381579920078730925885315196829948431464487738667554857248765609589529140860275484786688 else 22163329580580053030292883896087222257128851547184994372438075877716064731136) else (if i.val < 87 then 44326659161160106060585767792174444514257703094369988744876151755432129462272 else (if i.val < 88 then 88653318322320212121171535584348889028515406188739977489752303510864258924544 else 177306636644640424242343070794553358900319665317336657146949267823876582146048))) else (if i.val < 91 then (if i.val < 90 then 347376267711948586270712955400208142716521103653214096216800889679177324691456 else 694752535423897172541425910800416285433042207306428192433601779358354649382912) else (if i.val < 92 then 1389505070847794345082851821600832570866084414612856384867203558716709298765824 else (if i.val < 93 then 2779010141695588690165703643201665141732168829225712769734407117433418597531648 else 5558020283391177380331407286403330283464337658451425539468814234866837195063296)))) else (if i.val < 99 then (if i.val < 96 then (if i.val < 95 then 11116040566782354760662814572806660566928675316902851078937628469733674390126592 else 22232081133564709521325629145613321133857350633805702157875256939467348780253184) else (if i.val < 97 then 44464162267129419042651258291226642267714701267611404315750513878934697560506368 else (if i.val < 98 then 88928324534258838085302516582453284535429402535222808631501027757869395121012736 else 177856649068517676170605033164906569070858805070445617263002055515738790242025472))) else (if i.val < 102 then (if i.val < 100 then 355713298137035352341210066329813138141717610140891234526004111031477580484050944 else (if i.val < 101 then 711426596274070704682420132659626276283435220281782469052008222062955160968101888 else 1422853192548141409364840265319252552566870440563564938104016444125910321936203776)) else (if i.val < 103 then 2845706385096282818729680530638505105133740881127129876208032888251820643872407552 else (if i.val < 104 then 5691412770192565637459361061277010210267481762254259752416065776503641287744815104 else 11382825540385131274918722122554020420534963524508519504832131553007282575489630208))))) else (if i.val < 115 then (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then 22765651080770262549837444245108040841069927049017039009664263106014565150979260416 else 45531302161540525099674888490216081682139854098034078019328526212029130301958520832) else (if i.val < 108 then 91062604323081050199349776980432163364279708196068156038657052424058260603917041664 else (if i.val < 109 then 182125208646162100398699553960864326728559416392136312077314104848116521207834083328 else 364250417292324200797399107921728653457118832784272624154628209696233042415668166656))) else (if i.val < 112 then (if i.val < 111 then 728500834584648401594798215843457306914237665568545248309256419392466084831336333312 else 1457001669169296803189596431686914613828475331137090496618512838784932169662672666624) else (if i.val < 113 then 2914003338338593606379192863373829227656950662274180993237025677569864339325345333248 else (if i.val < 114 then 5828006676677187212758385726747658455313901324548361986474051355139728678650690666496 else 11656013353354374425516771453495316910627802649096723972948102710279457357301381332992)))) else (if i.val < 120 then (if i.val < 117 then (if i.val < 116 then 23312026706708748851033542906990633821255605298193447945896205420558914714602762665984 else 46624053413417497702067085813981267642511210596386895891792410841117829429205525331968) else (if i.val < 118 then 93248106826834995404134171627962535285022421192773791783584821682235658858411050663936 else (if i.val < 119 then 186496213653669990808268343255925070570044842385547583567169643364471317716822101327872 else 372992427307339981616536686511850141140089684771095167134339286728942635433644202655744))) else (if i.val < 123 then (if i.val < 121 then 745984854614679963233073373023700282280179369542190334268678573457885270867288405311488 else (if i.val < 122 then 1491969709229359926466146746047400564560358739084380668537357146915770541734576810622976 else 2983939418458719852932293492094801129120717478168761337074714293831541083469153621245952)) else (if i.val < 124 then 5967878836917439705864586984189602258241434956337522674149428587663082166938307242491904 else (if i.val < 125 then 11935757673834879411729173968379204516482869912675045348298857175326164333876614484983808 else 23871515347669758823458347936758409032965739825350090696597714350652328667753228969967616)))))) else (if i.val < 147 then (if i.val < 136 then (if i.val < 131 then (if i.val < 128 then (if i.val < 127 then 47743030695339517646916695873516818065931479650700181393195428701304657335506457939935232 else 95486061390679035293833391747033636131862959301400362786390857402609314671012915879870464) else (if i.val < 129 then 190972122781358070587666783494067272263725918602800725572781714805218629342025831759740928 else (if i.val < 130 then 381944245562716141175333566988134544527451837205601451145563429610437258684051663519481856 else 763888491125432282350667133976269089054903674411202902291126859220874517368103327038963712))) else (if i.val < 133 then (if i.val < 132 then 1527776982250864564701334267952538178109807348822405804582253718441749034736206654077927424 else 3055553964501729129402668535905076356219614697644811609164507436883498069472413308155854848) else (if i.val < 134 then 6111107929003458258805337071810152712439229395289623218329014873766996138944826616311709696 else (if i.val < 135 then 12222215858006916517610674143620305424878458790579246436658029747533992277889653232623419392 else 24444431716013833035221348287240610849756917581158492873316059495067984555779306465246838784)))) else (if i.val < 141 then (if i.val < 138 then (if i.val < 137 then 48888863432027666070442696574481221699513835162316985746632118990135969111558612930493677568 else 97777726864055332140885393148962443399027670324633971493264237980271938223117225860987355136) else (if i.val < 139 then 195555453728110664281770786297924886798055340649267942986528475960543876446234451721974710272 else (if i.val < 140 then 391110907456221328563541572595849773596110681298535885973056951921087752892468903443949420544 else 782221814912442657127083145191699547192221362597071771946113903842175505784937806887898841088))) else (if i.val < 144 then (if i.val < 142 then 1564443629824885314254166290383399094384442725194143543892227807684351011569875613775797682176 else (if i.val < 143 then 3128887259649770628508332580766798188768885450388287087784455615368702023139751227551595364352 else 6257774519299541257016665161533596377537770900776574175568911230737404046279502455103190728704)) else (if i.val < 145 then 12515549038599082514033330323067192755075541801553148351137822461474808092559004910206381457408 else (if i.val < 146 then 25031098077198165028066660646134385510151083603106296702275644922949616185118009820412762914816 else 50062196154396330056133321292268771020302166832068174247840142785755934537680680442973590126592))))) else (if i.val < 157 then (if i.val < 152 then (if i.val < 149 then (if i.val < 148 then 100124392308792660112266642584537542040604333664136348495680285571511869075361360885947180253184 else 200248784617585320224533285169075084081208667328272696991360571143023738150722721771894360506368) else (if i.val < 150 then 400497569235170640449066570338150168162417334656545393982721142286047476301445443543788721012736 else (if i.val < 151 then 800995138470341280898133140676300336324834669313090787965442284572094952602890887087577442025472 else 1601990276940682561796266281352600672649669338626181575930884569144189905205781774175154884050944))) else (if i.val < 154 then (if i.val < 153 then 3203980553881365123592532562705201345299338677252363151861769138288379810411563548350309768101888 else 6407961107762730247185065125410402690598677354504726303723538276576759620823127096700619536203776) else (if i.val < 155 then 12815922215525460494370130250820805381197354709009452607447076553153519241646254193401239072407552 else (if i.val < 156 then 25631844431050920988740260501641610762394709418018905214894153106307038483292508386802478144815104 else 51263688862101841977480521003283221524789418836037810429788306212614076966585016773604956289630208)))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then 102527377724203683954961042006566443049578837672075620859576612425228153933170033547209912579260416 else 205054755448407367909922084013132886099157675344151241719153224850456307866340067094419825158520832) else (if i.val < 160 then 410109510896814735819844168026265772198315350688302483438306449700912615732680134188839650317041664 else (if i.val < 161 then 820219021793629471639688336052531544396630701376604966876612899401825231465360268377679300634083328 else 1640438043587258943279376672105063088793261402753209933753225798803650462930720536755358601268166656))) else (if i.val < 165 then (if i.val < 163 then 3280876087174517886558753344210126177586522805506419867506451597607300925861441073510717202536333312 else (if i.val < 164 then 6561752174349035773117506688420252355173045611012839735012903195214601851722882147021434405072666624 else 13123504348698071546235013376840504710346091222025679470025806390429203703445764294042868810145333248)) else (if i.val < 166 then 26247008697396143092470026753681009420692182444051358940051612780858407406891528588085737620290666496 else (if i.val < 167 then 52494017394792286184940053507362018841384364888102717880103225561716814813783057176171475240581332992 else 104988034789584572369880107014724037682768729776205435760206451123433629627566114352342950481162665984))))))))
def xcoef (j : Fin 336) : BitVec 168 := BitVec.ofNat 168 (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 6351587838587834064977920 else 12703175677175668129955840) else (if j.val < 3 then 7427714468576662252242943 else (if j.val < 4 then 12278780804320532180928512 else 8994414602393323601221631))) else (if j.val < 7 then (if j.val < 6 then 10278968700587444653434880 else 2576938764669902931957759) else (if j.val < 8 then 2580775778621885405341696 else (if j.val < 9 then 1227815357885195095117824 else 2455630715770390190235648)))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then 4911261431540780380471296 else 9822522863081560760942592) else (if j.val < 13 then 4084260480180653669566463 else (if j.val < 14 then 756169547960522096412672 else 1512339095921044192825344))) else (if j.val < 18 then (if j.val < 16 then 3024678191842088385650688 else (if j.val < 17 then 302231454903657293676544 else 604462909807314587353088)) else (if j.val < 19 then 1208925819614629174706176 else (if j.val < 20 then 2417851639229258349412352 else 4835703278458516698824704))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then 9671406556917033397649408 else 3782027876858800345204735) else (if j.val < 24 then 151708953004002374617088 else (if j.val < 25 then 6050533575385491329863680 else 12101067150770982659727360))) else (if j.val < 28 then (if j.val < 27 then 2894224126216028036089855 else 3211800119615687703562240) else (if j.val < 29 then 6423600239231375407124480 else (if j.val < 30 then 12847200478462750814248960 else 3782027872355199711201279)))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then 151708943996800838174720 else 6050533593399885275942912) else (if j.val < 34 then 12101067186799770551885824 else (if j.val < 35 then 2894224198273605967890431 else 3211800263730912286640128))) else (if j.val < 39 then (if j.val < 37 then 6423600527461824573280256 else (if j.val < 38 then 12847201054923649146560512 else 3782029025276996375824383)) else (if j.val < 40 then 151706638153207508928512 else (if j.val < 41 then 303413276306415017857024 else 606826552612830035714048)))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then 5137934733362173993549824 else 10275869466724347987099648) else (if j.val < 45 then 2573102057244171174692863 else (if j.val < 46 then 2569560592233260732418048 else 1214830296926974647816192))) else (if j.val < 49 then (if j.val < 48 then 2429660593853949295632384 else 1530047898156637463052288) else (if j.val < 50 then 3060095796313274926104576 else (if j.val < 51 then 382511973413259458920448 else 765023946826518917840896)))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then 1530047893653037835681792 else 3060095787306075671363584) else (if j.val < 55 then 382511991427657968402432 else (if j.val < 56 then 765023982855315936804864 else 1530047965710631873609728))) else (if j.val < 60 then (if j.val < 58 then 3060095931421263747219456 else (if j.val < 59 then 382511703197281816690688 else 765023406394563633381376)) else (if j.val < 61 then 1530046812789127266762752 else (if j.val < 62 then 3060093625578254533525504 else 6120187251156509067051008))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then 12240374502313018134102016 else 8919963758643568415885311) else (if j.val < 66 then 10427576104868759403005952 else (if j.val < 67 then 2874154140721409975736319 else 3176382515109389947545600))) else (if j.val < 70 then (if j.val < 69 then 6352765030218779895091200 else 12705530060437559790182400) else (if j.val < 71 then 4103149946112132250421247 else (if j.val < 72 then 793948479823479258122240 else 1587896959646958516244480)))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then 3175793919293917032488960 else 0) else (if j.val < 76 then 0 else (if j.val < 77 then 0 else 0))) else (if j.val < 81 then (if j.val < 79 then 0 else (if j.val < 80 then 0 else 0)) else (if j.val < 82 then 0 else (if j.val < 83 then 0 else 0))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then 7582342187866818163484271043949803277117289264 else 15164684375733636326942407914564708186448191903) else (if j.val < 87 then 22925607433025291214416348881191408297848090639 else (if j.val < 88 then 45851214866050582428806549435797619012059817953 else 98571145340680705332272235966291824463901048051))) else (if j.val < 91 then (if j.val < 90 then 197142290681361410664531924007630049941054193177 else 97054694325568941544582821439289394066442420019) else (if j.val < 92 then 194109388651137883089165642878578788132884840038 else (if j.val < 93 then 91702516844367625509602026744542820050686509004 else 183405033688735251019184710675971806034577719193)))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then 119979779084790373120497136675632401042612883203 else 239959558169580746241001971405840655571327261176) else (if j.val < 97 then 1480909194445081866237271899096692663988464 else (if j.val < 98 then 2961818388890163725665488548009473587701278 else 5923636777780327451330977096018947175402556))) else (if j.val < 102 then (if j.val < 100 then 11847273555560654902661954192037894350805112 else (if j.val < 101 then 7606036724302574428473689964378961837936133056 else 15212073448605148856928037115644089609076967297)) else (if j.val < 103 then 30424146897210297713836731418174345151358635779 else (if j.val < 104 then 60848293794420595427673462836348690302717271558 else 121696587588841190855346925672697380605434543116))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then 243393175177682381710693851345394761210869086232 else 7582342187866818163503613857063637343912588080) else (if j.val < 108 then 15164684375733636326981093540792376320038789535 else (if j.val < 109 then 22925607433025291214338977628736072030666895375 else 45851214866050582428651806930886946477697427425))) else (if j.val < 112 then (if j.val < 111 then 91702429732101164857284271048660058888599556035 else 183404859464202329714560829889467365689948477560) else (if j.val < 113 then 119979430635568761645129013526416033650592432320 else (if j.val < 114 then 239958861271137523290258027052832067301184864640 else 7582255075558819141608194215742880201851269936)))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then 15164510151117638283190254258150862035916153247 else 22925258983793295126757299063453043462421622799) else (if j.val < 118 then 45850517967586590253488449800320889341206882273 else (if j.val < 119 then 91701035935173180506957556787527944615618465731 else 183402071870346361013907401367203137143986296952))) else (if j.val < 123 then (if j.val < 121 then 119985005820622243054866038825136876621956104384 else (if j.val < 122 then 239970011641244486109732077650273753243912208768 else 7604555815772744780556295410626252087305958192)) else (if j.val < 124 then 15209111631545489561086456647917605806825529759 else (if j.val < 125 then 30418223263090979122153570482721377546855760703 else 60836446526181958244307140965442755093711521406)))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then 114269134456180870456279693178041659858870140876 else 228538268912361740912540043542969485650944982937) else (if j.val < 129 then 22841979617180163233557262133726776319372229683 else (if j.val < 130 then 45683959234360326467088372385257801528085970841 else 98950257923652481043629965969711244618004958211))) else (if j.val < 133 then (if j.val < 132 then 197900515847304962087232887529962319984398966777 else 98571145340679407257767460062677180837889260787) else (if j.val < 134 then 197142290681358814515515577312240527608983222759 else (if j.val < 135 then 97054694325574133840139663113341042108417700047 else 194109388651148267680266774773789314451031189089)))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then 98571058228393475497520813438777678305227128051 else 197142116456786950995022284064441522543658957287) else (if j.val < 139 then 97054345876430406799153076617743031977769169103 else (if j.val < 140 then 194108691752860813598293601782593294189734127201 else 98569664431818567333574467456385637782633004275))) else (if j.val < 144 then (if j.val < 142 then 197139328863637134667129592099657441498470709735 else (if j.val < 143 then 97059921062730039454938460547311194068145664207 else 194119842125460078909864369641729618370487117409)) else (if j.val < 145 then 98591965177017097956716003174658286144138984691 else (if j.val < 146 then 197183930354034195913412663536202738221482670567 else 93134904503579904063237046503954483867342865407))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then 186269809007159808126474093007908967734685730814 else 121695280989953836731282494032232859891511790844) else (if j.val < 150 then 243390561979907673462557290009889866296922086918 else (if j.val < 151 then 7588265481703688704611710194200177968549150476 else 15176530963407377409197282687126286790255606247))) else (if j.val < 154 then (if j.val < 153 then 30353061926814754818375222561138739513715913679 else 60706123853629509636743650220278755415820460128) else (if j.val < 155 then 121412247707259019273487300440557510831640920256 else (if j.val < 156 then 242824495414518038546966899298600419610589103742 else 1895585546966704540871067760987450819279322316)))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 3791171093933409081742135521974901638558644632 else 0) else (if j.val < 160 then 0 else (if j.val < 161 then 0 else 0))) else (if j.val < 165 then (if j.val < 163 then 0 else (if j.val < 164 then 0 else 0)) else (if j.val < 166 then 0 else (if j.val < 167 then 0 else 0)))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then 7715763463727826737825790 else 15431526927455653475651580) else (if j.val < 171 then 19221837087412424971655175 else (if j.val < 172 then 19100861060990783148011535 else 18858909008147499500724255))) else (if j.val < 175 then (if j.val < 174 then 18375004902460932206149695 else 17407196691087797617000575) else (if j.val < 176 then 15471580268341528438702335 else (if j.val < 177 then 11600347422848990082105855 else 3857881731863913368912895)))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then 0 else 0) else (if j.val < 181 then 0 else (if j.val < 182 then 0 else 0))) else (if j.val < 186 then (if j.val < 184 then 0 else (if j.val < 185 then 0 else 0)) else (if j.val < 187 then 0 else (if j.val < 188 then 0 else 0))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then 0 else 0) else (if j.val < 192 then 0 else (if j.val < 193 then 0 else 0))) else (if j.val < 196 then (if j.val < 195 then 0 else 0) else (if j.val < 197 then 0 else (if j.val < 198 then 0 else 0)))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then 0 else 0) else (if j.val < 202 then 0 else (if j.val < 203 then 0 else 0))) else (if j.val < 207 then (if j.val < 205 then 0 else (if j.val < 206 then 0 else 0)) else (if j.val < 208 then 0 else (if j.val < 209 then 0 else 0)))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then 0 else 0) else (if j.val < 213 then 0 else (if j.val < 214 then 0 else 0))) else (if j.val < 217 then (if j.val < 216 then 0 else 0) else (if j.val < 218 then 0 else (if j.val < 219 then 0 else 0)))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then 0 else 0) else (if j.val < 223 then 0 else (if j.val < 224 then 0 else 0))) else (if j.val < 228 then (if j.val < 226 then 0 else (if j.val < 227 then 0 else 0)) else (if j.val < 229 then 0 else (if j.val < 230 then 0 else 0))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then 0 else 0) else (if j.val < 234 then 0 else (if j.val < 235 then 0 else 0))) else (if j.val < 238 then (if j.val < 237 then 0 else 0) else (if j.val < 239 then 0 else (if j.val < 240 then 0 else 0)))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then 0 else 0) else (if j.val < 244 then 0 else (if j.val < 245 then 0 else 0))) else (if j.val < 249 then (if j.val < 247 then 0 else (if j.val < 248 then 0 else 0)) else (if j.val < 250 then 0 else (if j.val < 251 then 0 else 0))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then 0 else 0) else (if j.val < 255 then 0 else (if j.val < 256 then 0 else 0))) else (if j.val < 259 then (if j.val < 258 then 0 else 0) else (if j.val < 260 then 0 else (if j.val < 261 then 0 else 0)))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then 0 else 0) else (if j.val < 265 then 0 else (if j.val < 266 then 0 else 0))) else (if j.val < 270 then (if j.val < 268 then 0 else (if j.val < 269 then 0 else 0)) else (if j.val < 271 then 0 else (if j.val < 272 then 0 else 0))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then 0 else 0) else (if j.val < 276 then 0 else (if j.val < 277 then 0 else 0))) else (if j.val < 280 then (if j.val < 279 then 0 else 0) else (if j.val < 281 then 0 else (if j.val < 282 then 0 else 0)))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then 0 else 0) else (if j.val < 286 then 0 else (if j.val < 287 then 0 else 0))) else (if j.val < 291 then (if j.val < 289 then 0 else (if j.val < 290 then 0 else 0)) else (if j.val < 292 then 0 else (if j.val < 293 then 0 else 0)))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then 0 else 0) else (if j.val < 297 then 0 else (if j.val < 298 then 0 else 0))) else (if j.val < 301 then (if j.val < 300 then 0 else 0) else (if j.val < 302 then 0 else (if j.val < 303 then 0 else 0)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then 0 else 0) else (if j.val < 307 then 0 else (if j.val < 308 then 0 else 0))) else (if j.val < 312 then (if j.val < 310 then 0 else (if j.val < 311 then 0 else 0)) else (if j.val < 313 then 0 else (if j.val < 314 then 0 else 0))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 0 else 0) else (if j.val < 318 then 0 else (if j.val < 319 then 0 else 0))) else (if j.val < 322 then (if j.val < 321 then 0 else 0) else (if j.val < 323 then 0 else (if j.val < 324 then 0 else 0)))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then 0 else 0) else (if j.val < 328 then 0 else (if j.val < 329 then 0 else 0))) else (if j.val < 333 then (if j.val < 331 then 0 else (if j.val < 332 then 0 else 0)) else (if j.val < 334 then 0 else (if j.val < 335 then 0 else 0)))))))))
def xrem (j : Fin 336) : BitVec 336 := BitVec.ofNat 336 (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1436452394149247611565320686543812768157993487855846471020574366646444307089652405557162996062486528 else 2872904788298495223130641373087625536315986975711692942041148733292888614179304811114325992124973056) else (if j.val < 3 then 137289370281419265711895684294579258598125700601427967903558962896895508214729081310040674720911720448 else (if j.val < 4 then 2776925161365875374497588730287200443694972324196452665040922327393864874017820660552887143961198592 else 137643689581620465078557344096693739464079005716708529455155674228583887233581289194207749507395878912))) else (if j.val < 7 then (if j.val < 6 then 2324654806730471657215797385860731613180406063960939037395776497374882497616400782601424358548176896 else 136192336193182982981777933125480927174025430714149162849365028086529620667132776554512048992215367680) else (if j.val < 8 then 583659021991581135208940247987765310656723596627323453631851874164218608404770348815537415011696640 else (if j.val < 9 then 277678331029667639945686723149668944292911183094584115910992188792113959975787076091381611315068928 else 555356662059335279891373446299337888585822366189168231821984377584227919951574152182763222630137856)))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then 1110713324118670559782746892598675777171644732378336463643968755168455839903148304365526445260275712 else 2221426648237341119565493785197351554343289464756672927287937510336911679806296608731052890520551424) else (if j.val < 13 then 136533226682620024748712199148023656874765664386823017280470207194367925265526450162074835864625610752 else (if j.val < 14 then 171012601124972311116084977791133610220726412892984188882761439469709896978109760423129891337142272 else 342025202249944622232169955582267220441452825785968377765522878939419793956219520846259782674284544))) else (if j.val < 18 then (if j.val < 16 then 684050404499889244464339911164534440882905651571936755531045757878839587912439041692519565348569088 else (if j.val < 17 then 68351585149469122636640864214743886392182184711972959958482850888765131284721598195765246748000256 else 136703170298938245273281728429487772784364369423945919916965701777530262569443196391530493496000512)) else (if j.val < 19 then 273406340597876490546563456858975545568728738847891839833931403555060525138886392783060986992001024 else (if j.val < 20 then 546812681195752981093126913717951091137457477695783679667862807110121050277772785566121973984002048 else 1093625362391505962186253827435902182274914955391567359335725614220242100555545571132243947968004096))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then 2187250724783011924372507654871804364549829910783134718671451228440484201111091142264487895936008192 else 136464874837748402820327936143152354147776276713296814908968924674760405420332991333356690186841358336) else (if j.val < 24 then 34309954344412601282180492544840931768967398495225051568570528950236711402236880959047545005277184 else (if j.val < 25 then 1368367038465653573768293472594487260868445829861414910733236800369208628690945082476582655838126080 else 2736734076931307147536586945188974521736891659722829821466473600738417257381890164953165311676252160))) else (if j.val < 28 then (if j.val < 27 then 136264092316030332689841442034126497125186480486719917216939940484624404459749386589053231262775377920 else 726369230591723713311036411018911137556127149961993135638959864883663241960341419908784051181322240) else (if j.val < 29 then 1452738461183447426622072822037822275112254299923986271277919729767326483920682839817568102362644480 else (if j.val < 30 then 2905476922366894853244145644075644550224508599847972542555839459534652967841365679635136204725288960 else 136464874836729884604504182292315504962698598656973462109488713211815887437140104343253242621022175232)))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then 34309952307376108926269908817105725386239617947566698072166337866450258621682358499386254059110400 else 1368367042539724494394416650212819821700503275951817778665488685469202748405678142039967726387068928) else (if j.val < 34 then 2736734085079448988788833300425639643401006551903635557330977370938405496811356284079935452774137856 else (if j.val < 35 then 136264092332326616858013157801032095098393845950337456766612764465844161133682859987479996585373335552 else 726369263184307591005605750662674439679771638724526791581426922224246486448004853443750077145284608))) else (if j.val < 39 then (if j.val < 37 then 1452738526368615182011211501325348879359543277449053583162853844448492972896009706887500154290569216 else (if j.val < 38 then 2905477052737230364022423002650697758719086554898107166325707688896985945792019413775000308581138432 else 136464875097470555626060737009464748661175862172581079335071958197800598890476870906059115687604912128)) else (if j.val < 40 then 34309430826034065813160474516892891407927797747028202992693420417118346799724608826095771840413696 else (if j.val < 41 then 68618861652068131626320949033785782815855595494056405985386840834236693599449217652191543680827392 else 137237723304136263252641898067571565631711190988112811970773681668473387198898435304383087361654784)))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then 1161976947540975085060036890408669636894571105879620847079027003309497532711198348062230888134475776 else 2323953895081950170120073780817339273789142211759241694158054006618995065422396696124461776268951552) else (if j.val < 45 then 136191468497150526330729942385951170041650220584201565560648547527679061298997305181139572122340818944 else (if j.val < 46 then 581122635540165584272444996326980568726216602399652953514981641664280168647459096398943066337050624 else 274741676074147615376314825286962170233114326887135995954607797356811342090245647115527183948316672))) else (if j.val < 49 then (if j.val < 48 then 549483352148295230752629650573924340466228653774271991909215594713622684180491294231054367896633344 else 346030161642034076306347256751474776696285666812427112382685331668452374105701328029192772229529600) else (if j.val < 50 then 692060323284068152612694513502949553392571333624854224765370663336904748211402656058385544459059200 else (if j.val < 51 then 86507540155879022034776053404312351249149135228553041379263199565001623986550543875730709273378816 else 173015080311758044069552106808624702498298270457106082758526399130003247973101087751461418546757632)))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then 346030160623516088139104213617249404996596540914212165517052798260006495946202175502922837093515264 else 692060321247032176278208427234498809993193081828424331034105596520012991892404351005845674187030528) else (if j.val < 55 then 86507544229950974703748225941213838047905638821412828841793333198785136624396038253358621170597888 else (if j.val < 56 then 173015088459901949407496451882427676095811277642825657683586666397570273248792076506717242341195776 else 346030176919803898814992903764855352191622555285651315367173332795140546497584153013434484682391552))) else (if j.val < 60 then (if j.val < 58 then 692060353839607797629985807529710704383245110571302630734346665590281092995168306026868969364783104 else (if j.val < 59 then 86507479044799732000193465350790049267801581335656229441311195058248934416450276572082772465680384 else 173014958089599464000386930701580098535603162671312458882622390116497868832900553144165544931360768)) else (if j.val < 61 then 346029916179198928000773861403160197071206325342624917765244780232995737665801106288331089862721536 else (if j.val < 62 then 692059832358397856001547722806320394142412650685249835530489560465991475331602212576662179725443072 else 1384119664716795712003095445612640788284825301370499671060979120931982950663204425153324359450886144))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then 2768239329433591424006190891225281576569650602740999342121958241863965901326408850306648718901772288 else 137626852045012525357593591550828122582861823662533758803412202345226983347497910197593819425443676160) else (if j.val < 66 then 2358263325905994942987595108765610631267969054182249946082650488494300041366341070061767824561405952 else (if j.val < 67 then 136259553359875284924088994706681868590335291919500213252359369798312787662078017812443266375560986624 else 718359311799604178198477072815306199619964929311218089459611107965410653101210823645301138564055040))) else (if j.val < 70 then (if j.val < 69 then 1436718623599208356396954145630612399239929858622436178919222215930821306202421647290602277128110080 else 2873437247198416712793908291261224798479859717244872357838444431861642612404843294581204554256220160) else (if j.val < 71 then 136537498656691866568876989202037078367665175773367515590467612372548473086231706302438587517974347776 else (if j.val < 72 then 179556549268655951445665085817976596019749185981980808877571795830805538388622041150633198034616320 else 359113098537311902891330171635953192039498371963961617755143591661611076777244082301266396069232640)))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then 718226197074623805782660343271906384078996743927923235510287183323222153554488164602532792138465280 else 18889465931478580854784) else (if j.val < 76 then 37778931862957161709568 else (if j.val < 77 then 75557863725914323419136 else 151115727451828646838272))) else (if j.val < 81 then (if j.val < 79 then 302231454903657293676544 else (if j.val < 80 then 604462909807314587353088 else 1208925819614629174706176)) else (if j.val < 82 then 2417851639229258349412352 else (if j.val < 83 then 4835703278458516698824704 else 9671406556917033397649408))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then 74094173727272412896387993344665462031941874329816293061972624114775357295247395081513042375887290368 else 137899429838327770710270443853527189011439651216771387972144968459902795661066431117281294499599876096) else (if j.val < 87 then 69924538569594076826503890531464104699585375599067342555462734280037492571355523195824969505451278336 else (if j.val < 88 then 7074923059339133101600243673718755599579654341189918735022005875287598677849993673549085611864883200 else 86601470951874016514124048577834743790196009970046022837482905994991568459432595558836272313642516480))) else (if j.val < 91 then (if j.val < 90 then 113704891085447682345944175574973202285322687904713366185385002600048824152999196737029633443069165568 else 13331964119529418292555678665425549045942187439246047845193542333358131532510356629922837463054680064) else (if j.val < 92 then 26663928239058836585111357330851098091884374878492095690387084666716263065020713259845674926109360128 else (if j.val < 93 then 125779983889306934964209656017223626790350993977600902674148286799037702206090222582488357639771127808 else 111575921392501106768579176735925063530361358351222772460041495617212454065955638544770872444637413376)))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then 83167796398889450377318218173327937010382087098466512031827913253561957785686470469335902054369984512 else 106628479115392373739143437201285929781442699665303230976615301024726053614234119190639496348464840704) else (if j.val < 97 then 821287011476234098586136810006776401706330105534248610446643222161412914244754467531961185320566784 else (if j.val < 98 then 131337702792860904641088773386263833275842469844020436156085496717697389479175754709548726960072425472 else 122691359199609046122337411474005476501344310084061839423915915454531828612126702798891611085240008704))) else (if j.val < 102 then (if j.val < 100 then 105398672013105329084834687649488762952347990564144645959576752928200706878028598977577379335575175168 else (if j.val < 101 then 3280876087174517886558753344210126177586522805506419867506451597607299658210840845281315705833127936 else 6561752174349035773117506688420252355173045611012839735012903195214599316421681690562631411666255872)) else (if j.val < 103 then 13123504348698071546235013376840504710346091222025679470025806390429198632843363381125262823332511744 else (if j.val < 104 then 26247008697396143092470026753681009420692182444051358940051612780858397265686726762250525646665023488 else 52494017394792286184940053507362018841384364888102717880103225561716794531373453524501051293330046976))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then 104988034789584572369880107014724037682768729776205435760206451123433589062746907049002102586660093952 else 4102150534216031316467914613739576716745044381384875342286351148811572177210209893224340946044321792) else (if j.val < 108 then 137899429838327770710270466016856769591492681509655284059367225588754180586745288715766112504063721472 else (if j.val < 109 then 69924538569594076826503846204804943539479315013299550381018220022334722719997807998855333496523587584 else 7074923059339133101600332327037077919791775512725128939491877679546078237248248699035325710989262848))) else (if j.val < 112 then (if j.val < 111 then 14149846118678266203200664654074155839583551025450257878983755359092156474496497398070651421978525696 else 105500803612472682847502984213198673708912100756614162923727248962247019511471400669591277120960593920) else (if j.val < 113 then 71017560838832602535165833127875157367483571909249292959199419943631088676717994718976711407016345600 else (if j.val < 114 then 2051075291552441910491530957228124684626514214519553030143761906399227007211182817747579979127848960 else 4102150583104883820983061914456249369253028429039106060287523812798454014422365635495159958255697920)))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then 137899429936105522343354174035787816963594463586231388006579818854391839965998762752854151165766533120 else 69924538374038672636449933679125465687833105570341079899911535696789345926883164916274318215473004544) else (if j.val < 118 then 7074922668228324721492507275678122216499356626808187977278509028455324651018962533873295148888096768 else (if j.val < 119 then 14149845336456649442985014551356244432998713253616375954557018056910649302037925067746590297776193536 else 105500805176915916367934284418634496522081776300281903388554526272163342597431221869711084874444570624))) else (if j.val < 123 then (if j.val < 121 then 71017563967719069576028433538746802993822922996584773888853974563463734848637637119216326913984299008 else (if j.val < 122 then 2051081549325375992216731778971415937305216389190514889452871146064519351050467618226810993063755776 else 4102163098650751984433463557942831874610432778381029778905742292129038702100935236453621986127511552)) else (if j.val < 124 then 137899454967209940412783426882135944221650675189713998493003694857632641054888116247392048561686315008 else (if j.val < 125 then 135814863548307117665726718465749698392960720775448964097752311734402331763551425874578254288467787776 else 131645680710501472171613301632977206735580811946918895307249545487941713180878045128950665742030733312)))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then 55774893481966804082881632391957276293889609816163146476131541951538654784642944446782015025295917056 else 111549786963933608165763264783914552587779219632326292952263083903077309569285888893564030050591834112) else (if j.val < 129 then 17225654882914102817171625829039556327416247113194426362119909192595763393989679124237753685163114496 else (if j.val < 130 then 111652421140931627708863043586256810370150276046036094329601869647010705932096387276758107669873557504 else 17430521174801790459438584051280824299395396164332704536578256432408304297164614972624071032530010112))) else (if j.val < 133 then (if j.val < 132 then 112062957848923705835730856634085316399959613210659218156817158864992666485189133580479197052628107264 else 16609447758817635662704627124920615429373153522001117478675392833389762449669680616005596276777287680) else (if j.val < 134 then 33218895517635271325409254249841230858746307044002234957350785666779524899339361232011192553554575360 else (if j.val < 135 then 138891426179008048269090021244320588805150332981860071354435349997776865696487293122372849496041193472 else 8304723854964386115338480527238959427445965911243641158179249821780722977397886771170102393618563072)))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then 16609447709928772230676961054477918854891931822487282316358499643561445954795773542340204787237126144 else 33218895419857544461353922108955837709783863644974564632716999287122891909591547084680409574474252288) else (if j.val < 139 then 138891426374563501997200685526091375103075219779915409080699648095284295268613255984468376142336753664 else (if j.val < 140 then 8304724246075293571559809090780532023295739507354316610707846016795582121649812495361155686209683456 else 16609448492150587143119618181561064046591479014708633221415692033591164243299624990722311372419366912))) else (if j.val < 144 then (if j.val < 142 then 33218896984301174286239236363122128093182958029417266442831384067182328486599249981444622744838733824 else (if j.val < 143 then 138891423245676242347430057017758794336277031011029958692418483946272039596683203269883320811766415360 else 8304717988300774272018552074115370489699361969583415834145517718771070777789707066191045025069006848)) else (if j.val < 145 then 16609435976601548544037104148230740979398723939166831668291035437542141555579414132382090050138013696 else (if j.val < 146 then 33218871953203097088074208296461481958797447878333663336582070875084283111158828264764180100276027392 else 66437743906406194176148416592922963917594895756667326673164141750168566222317656529528360200552054784))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then 132875487812812388352296833185845927835189791513334653346328283500337132444635313059056720401104109568 else 53315304406220777240736598663062676567616035920357376622424483314422884707506198659036809553216798720) else (if j.val < 150 then 26349668003371818308410841133515225025618489193519944105249181332263713322729143053592575235319660544 else (if j.val < 151 then 126793007156022537939083336550217374587435048117331154586699941980988570361229277303771755888720740352 else 33321831241591723630164071018584257686044114729268869783101313082824701622102606347554568565373796352))) else (if j.val < 154 then (if j.val < 153 then 66643662483183447260328142037168515372088229458537739566202626165649403244205212695109137130747592704 else 513170883462320733248029447009954643902743890439199549289507349132525972053970075514305703422459904) else (if j.val < 155 then 1026341766924641466496058894019909287805487780878399098579014698265051944107940151028611406844919808 else (if j.val < 156 then 131747812303757719376908617554290099048040785194708737132350239669904667538902126076542027403121131520 else 123511578221402675593977099810058008045740940785438441376445401358946384731579445532878211971337420800)))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 107039110056692588028114064321593826041141251966897849864635724737029819116934084445550581107769999360 else 365375409332725729550921208179070754913983135744) else (if j.val < 160 then 730750818665451459101842416358141509827966271488 else (if j.val < 161 then 1461501637330902918203684832716283019655932542976 else 2923003274661805836407369665432566039311865085952))) else (if j.val < 165 then (if j.val < 163 then 5846006549323611672814739330865132078623730171904 else (if j.val < 164 then 11692013098647223345629478661730264157247460343808 else 23384026197294446691258957323460528314494920687616)) else (if j.val < 166 then 46768052394588893382517914646921056628989841375232 else (if j.val < 167 then 93536104789177786765035829293842113257979682750464 else 187072209578355573530071658587684226515959365500928)))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then 132980012962617427211184085164422850699323249288498017994404343193695061533569917384666330698145071104 else 125975979539122091262528035030323511348305868973017003100553608406527172720915028149126818561385299968) else (if j.val < 171 then 34968652090967662133910596157063775004699395032468673941844734471104864797622970350108706035199901696 else (if j.val < 172 then 69937304181935324267821192314127550009398790064937347883689468942209729595245940700217412070399803392 else 139874608363870648535642384628255100018797580129874695767378937884419459190491881400434824140799606784))) else (if j.val < 175 then (if j.val < 174 then 139765170341628533911444633957988009987254530655770358646502797787975968034758956180663805446694371328 else 139546294297144304663049132617453829924168431707561684404750517595088985723293105741121768058483900416) else (if j.val < 176 then 139108542208175846166258129936385469797996233811144335921245957209315021100361404862037693282062958592 else (if j.val < 177 then 138233038030238929172676124574248749545651838018309638954236836437767091854498003103869543729221074944 else 136482029674365095185512113849975309040963046432640245020218594894671233362771199587533244623537307648)))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then 383123885216472214589586756787577295904684780545900544 else 766247770432944429179173513575154591809369561091801088) else (if j.val < 181 then 1532495540865888858358347027150309183618739122183602176 else (if j.val < 182 then 3064991081731777716716694054300618367237478244367204352 else 6129982163463555433433388108601236734474956488734408704))) else (if j.val < 186 then (if j.val < 184 then 12259964326927110866866776217202473468949912977468817408 else (if j.val < 185 then 24519928653854221733733552434404946937899825954937634816 else 49039857307708443467467104868809893875799651909875269632)) else (if j.val < 187 then 98079714615416886934934209737619787751599303819750539264 else (if j.val < 188 then 196159429230833773869868419475239575503198607639501078528 else 392318858461667547739736838950479151006397215279002157056))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then 784637716923335095479473677900958302012794430558004314112 else 1569275433846670190958947355801916604025588861116008628224) else (if j.val < 192 then 3138550867693340381917894711603833208051177722232017256448 else (if j.val < 193 then 6277101735386680763835789423207666416102355444464034512896 else 12554203470773361527671578846415332832204710888928069025792))) else (if j.val < 196 then (if j.val < 195 then 25108406941546723055343157692830665664409421777856138051584 else 50216813883093446110686315385661331328818843555712276103168) else (if j.val < 197 then 100433627766186892221372630771322662657637687111424552206336 else (if j.val < 198 then 200867255532373784442745261542645325315275374222849104412672 else 401734511064747568885490523085290650630550748445698208825344)))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then 803469022129495137770981046170581301261101496891396417650688 else 1606938044258990275541962092341162602522202993782792835301376) else (if j.val < 202 then 3213876088517980551083924184682325205044405987565585670602752 else (if j.val < 203 then 6427752177035961102167848369364650410088811975131171341205504 else 12855504354071922204335696738729300820177623950262342682411008))) else (if j.val < 207 then (if j.val < 205 then 25711008708143844408671393477458601640355247900524685364822016 else (if j.val < 206 then 51422017416287688817342786954917203280710495801049370729644032 else 102844034832575377634685573909834406561420991602098741459288064)) else (if j.val < 208 then 205688069665150755269371147819668813122841983204197482918576128 else (if j.val < 209 then 411376139330301510538742295639337626245683966408394965837152256 else 822752278660603021077484591278675252491367932816789931674304512)))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then 1645504557321206042154969182557350504982735865633579863348609024 else 3291009114642412084309938365114701009965471731267159726697218048) else (if j.val < 213 then 6582018229284824168619876730229402019930943462534319453394436096 else (if j.val < 214 then 13164036458569648337239753460458804039861886925068638906788872192 else 26328072917139296674479506920917608079723773850137277813577744384))) else (if j.val < 217 then (if j.val < 216 then 52656145834278593348959013841835216159447547700274555627155488768 else 105312291668557186697918027683670432318895095400549111254310977536) else (if j.val < 218 then 210624583337114373395836055367340864637790190801098222508621955072 else (if j.val < 219 then 421249166674228746791672110734681729275580381602196445017243910144 else 842498333348457493583344221469363458551160763204392890034487820288)))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then 1684996666696914987166688442938726917102321526408785780068975640576 else 3369993333393829974333376885877453834204643052817571560137951281152) else (if j.val < 223 then 6739986666787659948666753771754907668409286105635143120275902562304 else (if j.val < 224 then 13479973333575319897333507543509815336818572211270286240551805124608 else 26959946667150639794667015087019630673637144422540572481103610249216))) else (if j.val < 228 then (if j.val < 226 then 53919893334301279589334030174039261347274288845081144962207220498432 else (if j.val < 227 then 107839786668602559178668060348078522694548577690162289924414440996864 else 215679573337205118357336120696157045389097155380324579848828881993728)) else (if j.val < 229 then 431359146674410236714672241392314090778194310760649159697657763987456 else (if j.val < 230 then 862718293348820473429344482784628181556388621521298319395315527974912 else 1725436586697640946858688965569256363112777243042596638790631055949824))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then 3450873173395281893717377931138512726225554486085193277581262111899648 else 6901746346790563787434755862277025452451108972170386555162524223799296) else (if j.val < 234 then 13803492693581127574869511724554050904902217944340773110325048447598592 else (if j.val < 235 then 27606985387162255149739023449108101809804435888681546220650096895197184 else 55213970774324510299478046898216203619608871777363092441300193790394368))) else (if j.val < 238 then (if j.val < 237 then 110427941548649020598956093796432407239217743554726184882600387580788736 else 220855883097298041197912187592864814478435487109452369765200775161577472) else (if j.val < 239 then 441711766194596082395824375185729628956870974218904739530401550323154944 else (if j.val < 240 then 883423532389192164791648750371459257913741948437809479060803100646309888 else 1766847064778384329583297500742918515827483896875618958121606201292619776)))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then 3533694129556768659166595001485837031654967793751237916243212402585239552 else 7067388259113537318333190002971674063309935587502475832486424805170479104) else (if j.val < 244 then 14134776518227074636666380005943348126619871175004951664972849610340958208 else (if j.val < 245 then 28269553036454149273332760011886696253239742350009903329945699220681916416 else 56539106072908298546665520023773392506479484700019806659891398441363832832))) else (if j.val < 249 then (if j.val < 247 then 113078212145816597093331040047546785012958969400039613319782796882727665664 else (if j.val < 248 then 226156424291633194186662080095093570025917938800079226639565593765455331328 else 452312848583266388373324160190187140051835877600158453279131187530910662656)) else (if j.val < 250 then 904625697166532776746648320380374280103671755200316906558262375061821325312 else (if j.val < 251 then 1809251394333065553493296640760748560207343510400633813116524750123642650624 else 3618502788666131106986593281521497120414687020801267626233049500247285301248))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then 7237005577332262213973186563042994240829374041602535252466099000494570602496 else 14474011154664524427946373126085988481658748083205070504932198000989141204992) else (if j.val < 255 then 28948022309329048855892746252171976963317496166410141009864396001978282409984 else (if j.val < 256 then 57896044618658097711785492504343953926634992332820282019728792003956564819968 else 115792089237316195423570985008687907853269984665640564039457584007913129639936))) else (if j.val < 259 then (if j.val < 258 then 231584178474632390847141970017375815706539969331281128078915168015826259279872 else 463168356949264781694283940034751631413079938662562256157830336031652518559744) else (if j.val < 260 then 926336713898529563388567880069503262826159877325124512315660672063305037119488 else (if j.val < 261 then 1852673427797059126777135760139006525652319754650249024631321344126610074238976 else 3705346855594118253554271520278013051304639509300498049262642688253220148477952)))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then 7410693711188236507108543040556026102609279018600996098525285376506440296955904 else 14821387422376473014217086081112052205218558037201992197050570753012880593911808) else (if j.val < 265 then 29642774844752946028434172162224104410437116074403984394101141506025761187823616 else (if j.val < 266 then 59285549689505892056868344324448208820874232148807968788202283012051522375647232 else 118571099379011784113736688648896417641748464297615937576404566024103044751294464))) else (if j.val < 270 then (if j.val < 268 then 237142198758023568227473377297792835283496928595231875152809132048206089502588928 else (if j.val < 269 then 474284397516047136454946754595585670566993857190463750305618264096412179005177856 else 948568795032094272909893509191171341133987714380927500611236528192824358010355712)) else (if j.val < 271 then 1897137590064188545819787018382342682267975428761855001222473056385648716020711424 else (if j.val < 272 then 3794275180128377091639574036764685364535950857523710002444946112771297432041422848 else 7588550360256754183279148073529370729071901715047420004889892225542594864082845696))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then 15177100720513508366558296147058741458143803430094840009779784451085189728165691392 else 30354201441027016733116592294117482916287606860189680019559568902170379456331382784) else (if j.val < 276 then 60708402882054033466233184588234965832575213720379360039119137804340758912662765568 else (if j.val < 277 then 121416805764108066932466369176469931665150427440758720078238275608681517825325531136 else 242833611528216133864932738352939863330300854881517440156476551217363035650651062272))) else (if j.val < 280 then (if j.val < 279 then 485667223056432267729865476705879726660601709763034880312953102434726071301302124544 else 971334446112864535459730953411759453321203419526069760625906204869452142602604249088) else (if j.val < 281 then 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176 else (if j.val < 282 then 3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 else 7770675568902916283677847627294075626569627356208558085007249638955617140820833992704)))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then 15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 else 31082702275611665134711390509176302506278509424834232340028998555822468563283335970816) else (if j.val < 286 then 62165404551223330269422781018352605012557018849668464680057997111644937126566671941632 else (if j.val < 287 then 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 else 248661618204893321077691124073410420050228075398673858720231988446579748506266687766528))) else (if j.val < 291 then (if j.val < 289 then 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 else (if j.val < 290 then 994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 else 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224)) else (if j.val < 292 then 3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448 else (if j.val < 293 then 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896 else 15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792)))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584 else 63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168) else (if j.val < 297 then 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336 else (if j.val < 298 then 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672 else 509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344))) else (if j.val < 301 then (if j.val < 300 then 1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688 else 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376) else (if j.val < 302 then 4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752 else (if j.val < 303 then 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504 else 16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016 else 65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032) else (if j.val < 307 then 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064 else (if j.val < 308 then 260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128 else 521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728256))) else (if j.val < 312 then (if j.val < 310 then 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512 else (if j.val < 311 then 2085924839766513752338888384931203236916703635113918720651407820138886450957656787131798913024 else 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048)) else (if j.val < 313 then 8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096 else (if j.val < 314 then 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192 else 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768 else 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536) else (if j.val < 318 then 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072 else (if j.val < 319 then 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144 else 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))) else (if j.val < 322 then (if j.val < 321 then 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 else 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152) else (if j.val < 323 then 8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304 else (if j.val < 324 then 17087896287367280659160173649356416916821636178853222159576332862577757806245124400183696695492608 else 34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216)))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then 68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 else 136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864) else (if j.val < 328 then 273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728 else (if j.val < 329 then 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456 else 1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912))) else (if j.val < 333 then (if j.val < 331 then 2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 else (if j.val < 332 then 4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 else 8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296)) else (if j.val < 334 then 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592 else (if j.val < 335 then 34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184 else 69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368)))))))))
def xD : Matrix (Fin 168) (Fin 336) (ZMod 2) := fun i j => entry (xcoef j) i
def xK : Matrix (Fin 336) (Fin 336) (ZMod 2) := fun i j => entry (xrem j) i
def zrowFormula (i : Fin 168) : BitVec 336 :=
  unit (eqb.symm (Sum.inl (er i-(0,0)))) ^^^
  unit (eqb.symm (Sum.inl (er i-(0,4)))) ^^^
  unit (eqb.symm (Sum.inl (er i-(0,62)))) ^^^
  unit (eqb.symm (Sum.inr (er i-(0,0)))) ^^^
  unit (eqb.symm (Sum.inr (er i-(0,1)))) ^^^
  unit (eqb.symm (Sum.inr (er i-(1,5))))
lemma zrow_formula_bits : ∀ i, zrow i = zrowFormula i := by decide +kernel
lemma zrow_formula_entry (i : Fin 168) (j : Fin 336) :
    entry (zrowFormula i) j = HZ polyA polyB (er i) (eqb j) := by
  cases hq : eqb j with
  | inl g =>
    have yes (t : Grp 2 84) : j = eqb.symm (Sum.inl (er i-t)) ↔ er i-g = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inl.injEq]
      constructor <;> intro h <;> linear_combination -h
    have no (t : Grp 2 84) : j ≠ eqb.symm (Sum.inr (er i-t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [zrowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HZ,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,Matrix.transpose_apply,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,4) (0,62) (er i-g) (by decide) (by decide) (by decide)
  | inr g =>
    have yes (t : Grp 2 84) : j = eqb.symm (Sum.inr (er i-t)) ↔ er i-g = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inr.injEq]
      constructor <;> intro h <;> linear_combination -h
    have no (t : Grp 2 84) : j ≠ eqb.symm (Sum.inl (er i-t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [zrowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HZ,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,Matrix.transpose_apply,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,1) (1,5) (er i-g) (by decide) (by decide) (by decide)
lemma zrow_entry (i : Fin 168) (j : Fin 336) : entry (zrow i) j = zH i j := by
  rw [zrow_formula_bits,zrow_formula_entry]
  exact congrFun (congrFun ztable i) j
lemma xdecomp_bits : ∀ j, combination zrow (xcoef j) ^^^ xrem j = unit j := by decide +kernel
lemma xdecomp : zH.transpose * xD + xK = 1 := by
  have h := decomposition zrow xcoef xrem xdecomp_bits
  have he : (Matrix.of fun i j => entry (zrow i) j) = zH := by
    apply Matrix.ext; intro i j; exact zrow_entry i j
  rw [he] at h
  exact h
def xneighbors (i : Fin 168) : List (Fin 336) := (if i.val < 84 then (if i.val < 42 then (if i.val < 21 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [0, 1, 89, 168, 172, 230] else [1, 2, 90, 169, 173, 231]) else (if i.val < 3 then [2, 3, 91, 170, 174, 232] else (if i.val < 4 then [3, 4, 92, 171, 175, 233] else [4, 5, 93, 172, 176, 234]))) else (if i.val < 7 then (if i.val < 6 then [5, 6, 94, 173, 177, 235] else [6, 7, 95, 174, 178, 236]) else (if i.val < 8 then [7, 8, 96, 175, 179, 237] else (if i.val < 9 then [8, 9, 97, 176, 180, 238] else [9, 10, 98, 177, 181, 239])))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then [10, 11, 99, 178, 182, 240] else [11, 12, 100, 179, 183, 241]) else (if i.val < 13 then [12, 13, 101, 180, 184, 242] else (if i.val < 14 then [13, 14, 102, 181, 185, 243] else [14, 15, 103, 182, 186, 244]))) else (if i.val < 18 then (if i.val < 16 then [15, 16, 104, 183, 187, 245] else (if i.val < 17 then [16, 17, 105, 184, 188, 246] else [17, 18, 106, 185, 189, 247])) else (if i.val < 19 then [18, 19, 107, 186, 190, 248] else (if i.val < 20 then [19, 20, 108, 187, 191, 249] else [20, 21, 109, 188, 192, 250]))))) else (if i.val < 31 then (if i.val < 26 then (if i.val < 23 then (if i.val < 22 then [21, 22, 110, 189, 193, 251] else [22, 23, 111, 168, 190, 194]) else (if i.val < 24 then [23, 24, 112, 169, 191, 195] else (if i.val < 25 then [24, 25, 113, 170, 192, 196] else [25, 26, 114, 171, 193, 197]))) else (if i.val < 28 then (if i.val < 27 then [26, 27, 115, 172, 194, 198] else [27, 28, 116, 173, 195, 199]) else (if i.val < 29 then [28, 29, 117, 174, 196, 200] else (if i.val < 30 then [29, 30, 118, 175, 197, 201] else [30, 31, 119, 176, 198, 202])))) else (if i.val < 36 then (if i.val < 33 then (if i.val < 32 then [31, 32, 120, 177, 199, 203] else [32, 33, 121, 178, 200, 204]) else (if i.val < 34 then [33, 34, 122, 179, 201, 205] else (if i.val < 35 then [34, 35, 123, 180, 202, 206] else [35, 36, 124, 181, 203, 207]))) else (if i.val < 39 then (if i.val < 37 then [36, 37, 125, 182, 204, 208] else (if i.val < 38 then [37, 38, 126, 183, 205, 209] else [38, 39, 127, 184, 206, 210])) else (if i.val < 40 then [39, 40, 128, 185, 207, 211] else (if i.val < 41 then [40, 41, 129, 186, 208, 212] else [41, 42, 130, 187, 209, 213])))))) else (if i.val < 63 then (if i.val < 52 then (if i.val < 47 then (if i.val < 44 then (if i.val < 43 then [42, 43, 131, 188, 210, 214] else [43, 44, 132, 189, 211, 215]) else (if i.val < 45 then [44, 45, 133, 190, 212, 216] else (if i.val < 46 then [45, 46, 134, 191, 213, 217] else [46, 47, 135, 192, 214, 218]))) else (if i.val < 49 then (if i.val < 48 then [47, 48, 136, 193, 215, 219] else [48, 49, 137, 194, 216, 220]) else (if i.val < 50 then [49, 50, 138, 195, 217, 221] else (if i.val < 51 then [50, 51, 139, 196, 218, 222] else [51, 52, 140, 197, 219, 223])))) else (if i.val < 57 then (if i.val < 54 then (if i.val < 53 then [52, 53, 141, 198, 220, 224] else [53, 54, 142, 199, 221, 225]) else (if i.val < 55 then [54, 55, 143, 200, 222, 226] else (if i.val < 56 then [55, 56, 144, 201, 223, 227] else [56, 57, 145, 202, 224, 228]))) else (if i.val < 60 then (if i.val < 58 then [57, 58, 146, 203, 225, 229] else (if i.val < 59 then [58, 59, 147, 204, 226, 230] else [59, 60, 148, 205, 227, 231])) else (if i.val < 61 then [60, 61, 149, 206, 228, 232] else (if i.val < 62 then [61, 62, 150, 207, 229, 233] else [62, 63, 151, 208, 230, 234]))))) else (if i.val < 73 then (if i.val < 68 then (if i.val < 65 then (if i.val < 64 then [63, 64, 152, 209, 231, 235] else [64, 65, 153, 210, 232, 236]) else (if i.val < 66 then [65, 66, 154, 211, 233, 237] else (if i.val < 67 then [66, 67, 155, 212, 234, 238] else [67, 68, 156, 213, 235, 239]))) else (if i.val < 70 then (if i.val < 69 then [68, 69, 157, 214, 236, 240] else [69, 70, 158, 215, 237, 241]) else (if i.val < 71 then [70, 71, 159, 216, 238, 242] else (if i.val < 72 then [71, 72, 160, 217, 239, 243] else [72, 73, 161, 218, 240, 244])))) else (if i.val < 78 then (if i.val < 75 then (if i.val < 74 then [73, 74, 162, 219, 241, 245] else [74, 75, 163, 220, 242, 246]) else (if i.val < 76 then [75, 76, 164, 221, 243, 247] else (if i.val < 77 then [76, 77, 165, 222, 244, 248] else [77, 78, 166, 223, 245, 249]))) else (if i.val < 81 then (if i.val < 79 then [78, 79, 167, 224, 246, 250] else (if i.val < 80 then [79, 80, 84, 225, 247, 251] else [80, 81, 85, 168, 226, 248])) else (if i.val < 82 then [81, 82, 86, 169, 227, 249] else (if i.val < 83 then [82, 83, 87, 170, 228, 250] else [0, 83, 88, 171, 229, 251]))))))) else (if i.val < 126 then (if i.val < 105 then (if i.val < 94 then (if i.val < 89 then (if i.val < 86 then (if i.val < 85 then [5, 84, 85, 252, 256, 314] else [6, 85, 86, 253, 257, 315]) else (if i.val < 87 then [7, 86, 87, 254, 258, 316] else (if i.val < 88 then [8, 87, 88, 255, 259, 317] else [9, 88, 89, 256, 260, 318]))) else (if i.val < 91 then (if i.val < 90 then [10, 89, 90, 257, 261, 319] else [11, 90, 91, 258, 262, 320]) else (if i.val < 92 then [12, 91, 92, 259, 263, 321] else (if i.val < 93 then [13, 92, 93, 260, 264, 322] else [14, 93, 94, 261, 265, 323])))) else (if i.val < 99 then (if i.val < 96 then (if i.val < 95 then [15, 94, 95, 262, 266, 324] else [16, 95, 96, 263, 267, 325]) else (if i.val < 97 then [17, 96, 97, 264, 268, 326] else (if i.val < 98 then [18, 97, 98, 265, 269, 327] else [19, 98, 99, 266, 270, 328]))) else (if i.val < 102 then (if i.val < 100 then [20, 99, 100, 267, 271, 329] else (if i.val < 101 then [21, 100, 101, 268, 272, 330] else [22, 101, 102, 269, 273, 331])) else (if i.val < 103 then [23, 102, 103, 270, 274, 332] else (if i.val < 104 then [24, 103, 104, 271, 275, 333] else [25, 104, 105, 272, 276, 334]))))) else (if i.val < 115 then (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then [26, 105, 106, 273, 277, 335] else [27, 106, 107, 252, 274, 278]) else (if i.val < 108 then [28, 107, 108, 253, 275, 279] else (if i.val < 109 then [29, 108, 109, 254, 276, 280] else [30, 109, 110, 255, 277, 281]))) else (if i.val < 112 then (if i.val < 111 then [31, 110, 111, 256, 278, 282] else [32, 111, 112, 257, 279, 283]) else (if i.val < 113 then [33, 112, 113, 258, 280, 284] else (if i.val < 114 then [34, 113, 114, 259, 281, 285] else [35, 114, 115, 260, 282, 286])))) else (if i.val < 120 then (if i.val < 117 then (if i.val < 116 then [36, 115, 116, 261, 283, 287] else [37, 116, 117, 262, 284, 288]) else (if i.val < 118 then [38, 117, 118, 263, 285, 289] else (if i.val < 119 then [39, 118, 119, 264, 286, 290] else [40, 119, 120, 265, 287, 291]))) else (if i.val < 123 then (if i.val < 121 then [41, 120, 121, 266, 288, 292] else (if i.val < 122 then [42, 121, 122, 267, 289, 293] else [43, 122, 123, 268, 290, 294])) else (if i.val < 124 then [44, 123, 124, 269, 291, 295] else (if i.val < 125 then [45, 124, 125, 270, 292, 296] else [46, 125, 126, 271, 293, 297])))))) else (if i.val < 147 then (if i.val < 136 then (if i.val < 131 then (if i.val < 128 then (if i.val < 127 then [47, 126, 127, 272, 294, 298] else [48, 127, 128, 273, 295, 299]) else (if i.val < 129 then [49, 128, 129, 274, 296, 300] else (if i.val < 130 then [50, 129, 130, 275, 297, 301] else [51, 130, 131, 276, 298, 302]))) else (if i.val < 133 then (if i.val < 132 then [52, 131, 132, 277, 299, 303] else [53, 132, 133, 278, 300, 304]) else (if i.val < 134 then [54, 133, 134, 279, 301, 305] else (if i.val < 135 then [55, 134, 135, 280, 302, 306] else [56, 135, 136, 281, 303, 307])))) else (if i.val < 141 then (if i.val < 138 then (if i.val < 137 then [57, 136, 137, 282, 304, 308] else [58, 137, 138, 283, 305, 309]) else (if i.val < 139 then [59, 138, 139, 284, 306, 310] else (if i.val < 140 then [60, 139, 140, 285, 307, 311] else [61, 140, 141, 286, 308, 312]))) else (if i.val < 144 then (if i.val < 142 then [62, 141, 142, 287, 309, 313] else (if i.val < 143 then [63, 142, 143, 288, 310, 314] else [64, 143, 144, 289, 311, 315])) else (if i.val < 145 then [65, 144, 145, 290, 312, 316] else (if i.val < 146 then [66, 145, 146, 291, 313, 317] else [67, 146, 147, 292, 314, 318]))))) else (if i.val < 157 then (if i.val < 152 then (if i.val < 149 then (if i.val < 148 then [68, 147, 148, 293, 315, 319] else [69, 148, 149, 294, 316, 320]) else (if i.val < 150 then [70, 149, 150, 295, 317, 321] else (if i.val < 151 then [71, 150, 151, 296, 318, 322] else [72, 151, 152, 297, 319, 323]))) else (if i.val < 154 then (if i.val < 153 then [73, 152, 153, 298, 320, 324] else [74, 153, 154, 299, 321, 325]) else (if i.val < 155 then [75, 154, 155, 300, 322, 326] else (if i.val < 156 then [76, 155, 156, 301, 323, 327] else [77, 156, 157, 302, 324, 328])))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then [78, 157, 158, 303, 325, 329] else [79, 158, 159, 304, 326, 330]) else (if i.val < 160 then [80, 159, 160, 305, 327, 331] else (if i.val < 161 then [81, 160, 161, 306, 328, 332] else [82, 161, 162, 307, 329, 333]))) else (if i.val < 165 then (if i.val < 163 then [83, 162, 163, 308, 330, 334] else (if i.val < 164 then [0, 163, 164, 309, 331, 335] else [1, 164, 165, 252, 310, 332])) else (if i.val < 166 then [2, 165, 166, 253, 311, 333] else (if i.val < 167 then [3, 166, 167, 254, 312, 334] else [4, 84, 167, 255, 313, 335]))))))))
def xpos (j : Fin 336) : List (Fin 168) := (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [0, 83, 163] else [0, 1, 164]) else (if j.val < 3 then [1, 2, 165] else (if j.val < 4 then [2, 3, 166] else [3, 4, 167]))) else (if j.val < 7 then (if j.val < 6 then [4, 5, 84] else [5, 6, 85]) else (if j.val < 8 then [6, 7, 86] else (if j.val < 9 then [7, 8, 87] else [8, 9, 88])))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then [9, 10, 89] else [10, 11, 90]) else (if j.val < 13 then [11, 12, 91] else (if j.val < 14 then [12, 13, 92] else [13, 14, 93]))) else (if j.val < 18 then (if j.val < 16 then [14, 15, 94] else (if j.val < 17 then [15, 16, 95] else [16, 17, 96])) else (if j.val < 19 then [17, 18, 97] else (if j.val < 20 then [18, 19, 98] else [19, 20, 99]))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then [20, 21, 100] else [21, 22, 101]) else (if j.val < 24 then [22, 23, 102] else (if j.val < 25 then [23, 24, 103] else [24, 25, 104]))) else (if j.val < 28 then (if j.val < 27 then [25, 26, 105] else [26, 27, 106]) else (if j.val < 29 then [27, 28, 107] else (if j.val < 30 then [28, 29, 108] else [29, 30, 109])))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then [30, 31, 110] else [31, 32, 111]) else (if j.val < 34 then [32, 33, 112] else (if j.val < 35 then [33, 34, 113] else [34, 35, 114]))) else (if j.val < 39 then (if j.val < 37 then [35, 36, 115] else (if j.val < 38 then [36, 37, 116] else [37, 38, 117])) else (if j.val < 40 then [38, 39, 118] else (if j.val < 41 then [39, 40, 119] else [40, 41, 120])))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then [41, 42, 121] else [42, 43, 122]) else (if j.val < 45 then [43, 44, 123] else (if j.val < 46 then [44, 45, 124] else [45, 46, 125]))) else (if j.val < 49 then (if j.val < 48 then [46, 47, 126] else [47, 48, 127]) else (if j.val < 50 then [48, 49, 128] else (if j.val < 51 then [49, 50, 129] else [50, 51, 130])))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then [51, 52, 131] else [52, 53, 132]) else (if j.val < 55 then [53, 54, 133] else (if j.val < 56 then [54, 55, 134] else [55, 56, 135]))) else (if j.val < 60 then (if j.val < 58 then [56, 57, 136] else (if j.val < 59 then [57, 58, 137] else [58, 59, 138])) else (if j.val < 61 then [59, 60, 139] else (if j.val < 62 then [60, 61, 140] else [61, 62, 141]))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then [62, 63, 142] else [63, 64, 143]) else (if j.val < 66 then [64, 65, 144] else (if j.val < 67 then [65, 66, 145] else [66, 67, 146]))) else (if j.val < 70 then (if j.val < 69 then [67, 68, 147] else [68, 69, 148]) else (if j.val < 71 then [69, 70, 149] else (if j.val < 72 then [70, 71, 150] else [71, 72, 151])))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then [72, 73, 152] else [73, 74, 153]) else (if j.val < 76 then [74, 75, 154] else (if j.val < 77 then [75, 76, 155] else [76, 77, 156]))) else (if j.val < 81 then (if j.val < 79 then [77, 78, 157] else (if j.val < 80 then [78, 79, 158] else [79, 80, 159])) else (if j.val < 82 then [80, 81, 160] else (if j.val < 83 then [81, 82, 161] else [82, 83, 162]))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then [79, 84, 167] else [80, 84, 85]) else (if j.val < 87 then [81, 85, 86] else (if j.val < 88 then [82, 86, 87] else [83, 87, 88]))) else (if j.val < 91 then (if j.val < 90 then [0, 88, 89] else [1, 89, 90]) else (if j.val < 92 then [2, 90, 91] else (if j.val < 93 then [3, 91, 92] else [4, 92, 93])))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then [5, 93, 94] else [6, 94, 95]) else (if j.val < 97 then [7, 95, 96] else (if j.val < 98 then [8, 96, 97] else [9, 97, 98]))) else (if j.val < 102 then (if j.val < 100 then [10, 98, 99] else (if j.val < 101 then [11, 99, 100] else [12, 100, 101])) else (if j.val < 103 then [13, 101, 102] else (if j.val < 104 then [14, 102, 103] else [15, 103, 104]))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then [16, 104, 105] else [17, 105, 106]) else (if j.val < 108 then [18, 106, 107] else (if j.val < 109 then [19, 107, 108] else [20, 108, 109]))) else (if j.val < 112 then (if j.val < 111 then [21, 109, 110] else [22, 110, 111]) else (if j.val < 113 then [23, 111, 112] else (if j.val < 114 then [24, 112, 113] else [25, 113, 114])))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then [26, 114, 115] else [27, 115, 116]) else (if j.val < 118 then [28, 116, 117] else (if j.val < 119 then [29, 117, 118] else [30, 118, 119]))) else (if j.val < 123 then (if j.val < 121 then [31, 119, 120] else (if j.val < 122 then [32, 120, 121] else [33, 121, 122])) else (if j.val < 124 then [34, 122, 123] else (if j.val < 125 then [35, 123, 124] else [36, 124, 125])))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then [37, 125, 126] else [38, 126, 127]) else (if j.val < 129 then [39, 127, 128] else (if j.val < 130 then [40, 128, 129] else [41, 129, 130]))) else (if j.val < 133 then (if j.val < 132 then [42, 130, 131] else [43, 131, 132]) else (if j.val < 134 then [44, 132, 133] else (if j.val < 135 then [45, 133, 134] else [46, 134, 135])))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then [47, 135, 136] else [48, 136, 137]) else (if j.val < 139 then [49, 137, 138] else (if j.val < 140 then [50, 138, 139] else [51, 139, 140]))) else (if j.val < 144 then (if j.val < 142 then [52, 140, 141] else (if j.val < 143 then [53, 141, 142] else [54, 142, 143])) else (if j.val < 145 then [55, 143, 144] else (if j.val < 146 then [56, 144, 145] else [57, 145, 146]))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then [58, 146, 147] else [59, 147, 148]) else (if j.val < 150 then [60, 148, 149] else (if j.val < 151 then [61, 149, 150] else [62, 150, 151]))) else (if j.val < 154 then (if j.val < 153 then [63, 151, 152] else [64, 152, 153]) else (if j.val < 155 then [65, 153, 154] else (if j.val < 156 then [66, 154, 155] else [67, 155, 156])))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then [68, 156, 157] else [69, 157, 158]) else (if j.val < 160 then [70, 158, 159] else (if j.val < 161 then [71, 159, 160] else [72, 160, 161]))) else (if j.val < 165 then (if j.val < 163 then [73, 161, 162] else (if j.val < 164 then [74, 162, 163] else [75, 163, 164])) else (if j.val < 166 then [76, 164, 165] else (if j.val < 167 then [77, 165, 166] else [78, 166, 167])))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then [0, 22, 80] else [1, 23, 81]) else (if j.val < 171 then [2, 24, 82] else (if j.val < 172 then [3, 25, 83] else [0, 4, 26]))) else (if j.val < 175 then (if j.val < 174 then [1, 5, 27] else [2, 6, 28]) else (if j.val < 176 then [3, 7, 29] else (if j.val < 177 then [4, 8, 30] else [5, 9, 31])))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then [6, 10, 32] else [7, 11, 33]) else (if j.val < 181 then [8, 12, 34] else (if j.val < 182 then [9, 13, 35] else [10, 14, 36]))) else (if j.val < 186 then (if j.val < 184 then [11, 15, 37] else (if j.val < 185 then [12, 16, 38] else [13, 17, 39])) else (if j.val < 187 then [14, 18, 40] else (if j.val < 188 then [15, 19, 41] else [16, 20, 42]))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then [17, 21, 43] else [18, 22, 44]) else (if j.val < 192 then [19, 23, 45] else (if j.val < 193 then [20, 24, 46] else [21, 25, 47]))) else (if j.val < 196 then (if j.val < 195 then [22, 26, 48] else [23, 27, 49]) else (if j.val < 197 then [24, 28, 50] else (if j.val < 198 then [25, 29, 51] else [26, 30, 52])))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then [27, 31, 53] else [28, 32, 54]) else (if j.val < 202 then [29, 33, 55] else (if j.val < 203 then [30, 34, 56] else [31, 35, 57]))) else (if j.val < 207 then (if j.val < 205 then [32, 36, 58] else (if j.val < 206 then [33, 37, 59] else [34, 38, 60])) else (if j.val < 208 then [35, 39, 61] else (if j.val < 209 then [36, 40, 62] else [37, 41, 63])))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then [38, 42, 64] else [39, 43, 65]) else (if j.val < 213 then [40, 44, 66] else (if j.val < 214 then [41, 45, 67] else [42, 46, 68]))) else (if j.val < 217 then (if j.val < 216 then [43, 47, 69] else [44, 48, 70]) else (if j.val < 218 then [45, 49, 71] else (if j.val < 219 then [46, 50, 72] else [47, 51, 73])))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then [48, 52, 74] else [49, 53, 75]) else (if j.val < 223 then [50, 54, 76] else (if j.val < 224 then [51, 55, 77] else [52, 56, 78]))) else (if j.val < 228 then (if j.val < 226 then [53, 57, 79] else (if j.val < 227 then [54, 58, 80] else [55, 59, 81])) else (if j.val < 229 then [56, 60, 82] else (if j.val < 230 then [57, 61, 83] else [0, 58, 62]))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then [1, 59, 63] else [2, 60, 64]) else (if j.val < 234 then [3, 61, 65] else (if j.val < 235 then [4, 62, 66] else [5, 63, 67]))) else (if j.val < 238 then (if j.val < 237 then [6, 64, 68] else [7, 65, 69]) else (if j.val < 239 then [8, 66, 70] else (if j.val < 240 then [9, 67, 71] else [10, 68, 72])))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then [11, 69, 73] else [12, 70, 74]) else (if j.val < 244 then [13, 71, 75] else (if j.val < 245 then [14, 72, 76] else [15, 73, 77]))) else (if j.val < 249 then (if j.val < 247 then [16, 74, 78] else (if j.val < 248 then [17, 75, 79] else [18, 76, 80])) else (if j.val < 250 then [19, 77, 81] else (if j.val < 251 then [20, 78, 82] else [21, 79, 83]))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then [84, 106, 164] else [85, 107, 165]) else (if j.val < 255 then [86, 108, 166] else (if j.val < 256 then [87, 109, 167] else [84, 88, 110]))) else (if j.val < 259 then (if j.val < 258 then [85, 89, 111] else [86, 90, 112]) else (if j.val < 260 then [87, 91, 113] else (if j.val < 261 then [88, 92, 114] else [89, 93, 115])))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then [90, 94, 116] else [91, 95, 117]) else (if j.val < 265 then [92, 96, 118] else (if j.val < 266 then [93, 97, 119] else [94, 98, 120]))) else (if j.val < 270 then (if j.val < 268 then [95, 99, 121] else (if j.val < 269 then [96, 100, 122] else [97, 101, 123])) else (if j.val < 271 then [98, 102, 124] else (if j.val < 272 then [99, 103, 125] else [100, 104, 126]))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then [101, 105, 127] else [102, 106, 128]) else (if j.val < 276 then [103, 107, 129] else (if j.val < 277 then [104, 108, 130] else [105, 109, 131]))) else (if j.val < 280 then (if j.val < 279 then [106, 110, 132] else [107, 111, 133]) else (if j.val < 281 then [108, 112, 134] else (if j.val < 282 then [109, 113, 135] else [110, 114, 136])))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then [111, 115, 137] else [112, 116, 138]) else (if j.val < 286 then [113, 117, 139] else (if j.val < 287 then [114, 118, 140] else [115, 119, 141]))) else (if j.val < 291 then (if j.val < 289 then [116, 120, 142] else (if j.val < 290 then [117, 121, 143] else [118, 122, 144])) else (if j.val < 292 then [119, 123, 145] else (if j.val < 293 then [120, 124, 146] else [121, 125, 147])))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then [122, 126, 148] else [123, 127, 149]) else (if j.val < 297 then [124, 128, 150] else (if j.val < 298 then [125, 129, 151] else [126, 130, 152]))) else (if j.val < 301 then (if j.val < 300 then [127, 131, 153] else [128, 132, 154]) else (if j.val < 302 then [129, 133, 155] else (if j.val < 303 then [130, 134, 156] else [131, 135, 157])))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then [132, 136, 158] else [133, 137, 159]) else (if j.val < 307 then [134, 138, 160] else (if j.val < 308 then [135, 139, 161] else [136, 140, 162]))) else (if j.val < 312 then (if j.val < 310 then [137, 141, 163] else (if j.val < 311 then [138, 142, 164] else [139, 143, 165])) else (if j.val < 313 then [140, 144, 166] else (if j.val < 314 then [141, 145, 167] else [84, 142, 146]))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then [85, 143, 147] else [86, 144, 148]) else (if j.val < 318 then [87, 145, 149] else (if j.val < 319 then [88, 146, 150] else [89, 147, 151]))) else (if j.val < 322 then (if j.val < 321 then [90, 148, 152] else [91, 149, 153]) else (if j.val < 323 then [92, 150, 154] else (if j.val < 324 then [93, 151, 155] else [94, 152, 156])))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then [95, 153, 157] else [96, 154, 158]) else (if j.val < 328 then [97, 155, 159] else (if j.val < 329 then [98, 156, 160] else [99, 157, 161]))) else (if j.val < 333 then (if j.val < 331 then [100, 158, 162] else (if j.val < 332 then [101, 159, 163] else [102, 160, 164])) else (if j.val < 334 then [103, 161, 165] else (if j.val < 335 then [104, 162, 166] else [105, 163, 167])))))))))
lemma xpos_nodup : ∀ j, (xpos j).Nodup := by decide +kernel
lemma xpos_signature : ∀ j, signature unit (xpos j) = xmask j := by decide +kernel
lemma xpos_length : ∀ j, (xpos j).length = 3 := by decide +kernel
lemma entry_nonzero_iff {r : ℕ} (v : BitVec r) (i : Fin r) :
    entry v i ≠ 0 ↔ v.getLsbD i.val = true := by
  unfold entry
  cases v.getLsbD i.val <;> decide
lemma xpos_spec (j : Fin 336) : (xpos j).Nodup ∧ (xpos j).toFinset = Finset.univ.filter (fun i => (xmask j).getLsbD i.val) := by
  refine ⟨xpos_nodup j, ?_⟩
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
  rw [← entry_nonzero_iff]
  have he : entry (xmask j) i = if i ∈ xpos j then 1 else 0 := by
    rw [← xpos_signature,signature_entry unit (xpos j) (xpos_nodup j) i]
    simp [unit_entry]
  rw [he]
  by_cases hi : i ∈ xpos j <;> simp [hi]
lemma ones_card {r : ℕ} (v : BitVec r) :
    ones v = (Finset.univ.filter fun i : Fin r => v.getLsbD i.val).card := by
  rw [ones_eq,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases v.getLsbD i.val <;> rfl
lemma xthree (j : Fin 336) : ones (xmask j) = 3 := by
  rw [ones_card,← (xpos_spec j).2,List.toFinset_card_of_nodup (xpos_nodup j),xpos_length]
def xupdate (j : Fin 336) (sy : BitVec 168) (pc : ℕ) : ℕ :=
  pc + 3 - 2 * ((xpos j).map fun i => (sy.getLsbD i.val).toNat).sum
lemma xupdate_spec (j : Fin 336) (sy : BitVec 168) : xupdate j sy (ones sy) = ones (xmask j ^^^ sy) :=
  BB336Count.update_eq (xmask j) sy (xpos j) (xpos_spec j).1 (xpos_spec j).2 (xthree j)
lemma xones (j : Fin 336) : ones (xmask j) ≤ 3 := (xthree j).le
lemma xpos_cover : ∀ j, (xpos j).all (fun i => decide (j ∈ xneighbors i)) = true := by decide +kernel
lemma xcover (i : Fin 168) (j : Fin 336) (h : entry (xmask j) i = 1) : j ∈ xneighbors i := by
  have hb : (xmask j).getLsbD i.val = true := by
    cases he : (xmask j).getLsbD i.val with
    | true => rfl
    | false =>
      have hz : entry (xmask j) i = 0 := by dsimp only [entry]; rw [he]; rfl
      rw [hz] at h
      exact False.elim (zero_ne_one h)
  have hi : i ∈ (xpos j).toFinset := by rw [(xpos_spec j).2]; simpa using hb
  have hh := List.all_eq_true.mp (xpos_cover j) i (List.mem_toFinset.mp hi)
  exact of_decide_eq_true hh
lemma weight_equiv {a b : Type} [Fintype a] [Fintype b]
    (e : a ≃ b) (v : b → ZMod 2) : weight (v ∘ e) = weight v := by
  classical
  simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact e.sum_comp (fun j => if v j ≠ 0 then (1 : ℕ) else 0)

lemma unindex_kernel (H : Matrix (Grp 2 84) (Qubit 2 84) (ZMod 2))
    (v : Fin 336 → ZMod 2) (hv : H.submatrix er eqb *ᵥ v = 0) :
    H *ᵥ (v ∘ eqb.symm) = 0 := by
  have h := Matrix.submatrix_mulVec_equiv H v er eqb
  rw [hv] at h
  funext i
  have hi := congrFun h (er.symm i)
  simpa using hi.symm

lemma index_kernel (H : Matrix (Grp 2 84) (Qubit 2 84) (ZMod 2))
    (v : Qubit 2 84 → ZMod 2) (hv : H *ᵥ v = 0) :
    H.submatrix er eqb *ᵥ (v ∘ eqb) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ eqb) ∘ eqb.symm = v := by funext i; simp
  rw [he,hv]
  rfl

end BB336KernelData

set_option maxHeartbeats 0
namespace BB336High

def seek {r : ℕ} (s : BitVec r) : ℕ → ℕ
  | 0 => 0
  | fuel+1 => if s.getLsbD fuel then fuel else seek s fuel

lemma seek_spec {r : ℕ} (s : BitVec r) (fuel : ℕ)
    (hex : ∃ i, i < fuel ∧ s.getLsbD i = true) :
    seek s fuel < fuel ∧ s.getLsbD (seek s fuel) = true := by
  induction fuel with
  | zero => obtain ⟨i,hi,_⟩ := hex; omega
  | succ f ih =>
    rw [seek]
    cases hb : s.getLsbD f with
    | true => simp only [hb,ite_true]; exact ⟨by omega,True.intro⟩
    | false =>
      simp only [hb,Bool.false_eq_true,ite_false]
      have hh : ∃ i, i < f ∧ s.getLsbD i = true := by
        obtain ⟨i,hi,hbit⟩ := hex
        refine ⟨i,?_,hbit⟩
        by_contra hn
        have he : i = f := by omega
        subst i
        rw [hb] at hbit
        contradiction
      have h := ih hh
      exact ⟨by omega,h.2⟩

lemma seek_lt {r : ℕ} (s : BitVec r) (hs : s ≠ 0) :
    seek s r < r ∧ s.getLsbD (seek s r) = true := by
  apply seek_spec
  by_contra h
  apply hs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : s.getLsbD i ≠ true := by intro he; exact h ⟨i,hi,he⟩
  simpa using hn

def pick {r : ℕ} [NeZero r] (s : BitVec r) : Fin r :=
  if h : s = 0 then 0 else ⟨seek s r,(seek_lt s h).1⟩

lemma pick_spec {r : ℕ} [NeZero r] (s : BitVec r) (hs : s ≠ 0) :
    s.getLsbD (pick s).val = true := by
  simpa only [pick,dif_neg hs] using (seek_lt s hs).2
end BB336High

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB336Cert
namespace BB336Grow

open BB336Search

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) : ℕ → List (Fin n) → BitVec r → Bool
  | fuel, used, sy =>
    if 3 * fuel < ones sy then true
    else if sy = 0 then decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => (nbr (BB336High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr fuel (j :: used) (C j ^^^ sy)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) :
    check C K nbr fuel used sy =
      if 3 * fuel < ones sy then true
      else if sy = 0 then decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => (nbr (BB336High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr f (j :: used) (C j ^^^ sy) := by
  cases fuel <;> rfl

lemma step {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r)
    (hs : sy ≠ 0)
    (hc : ∀ j ∈ nbr (BB336High.pick sy), j ∉ used → check C K nbr fuel (j::used) (C j ^^^ sy) = true) :
    check C K nbr (fuel+1) used sy = true := by
  rw [check_eq]
  by_cases hp : 3*(fuel+1) < ones sy
  · simp only [if_pos hp]
  · rw [if_neg hp,if_neg hs]
    apply List.all_eq_true.mpr
    intro j hj
    by_cases hu : j ∈ used
    · simp [hu]
    · simpa only [if_neg hu] using hc j hj hu
end BB336Grow

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BB336Cert BB336Search
namespace BB336Grow

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
      (∀ i, ∑ j ∈ S, entry (C j) i = 0) ∧ (∀ i, ∑ j ∈ S, entry (K j) i = 0) := by
  classical
  induction fuel using Nat.strong_induction_on generalizing used with
  | h fuel ih =>
    have hbound := completion_bound C hC T hT fuel used hn hu hb
    rw [check_eq,if_neg (by omega : ¬ 3*fuel < ones (signature C used))] at hc
    by_cases hz : signature C used = 0
    · have hh : signature K used = 0 := by simpa [hz] using hc
      refine ⟨used.toFinset,hu,Finset.Subset.refl _,?_,?_⟩
      · intro i
        rw [← signature_entry C used hn i,hz]
        simp [entry]
      · intro i
        rw [← signature_entry K used hn i,hh]
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
        let i := BB336High.pick (signature C used)
        have hp : entry (signature C used) i = 1 := by
          simp [entry,i,BB336High.pick_spec _ hz]
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
        obtain ⟨S,hST,hUS,hSC,hSK⟩ := ih f (by omega) (j::used)
          (List.nodup_cons.mpr ⟨hju,hn⟩) hsub (by simp only [List.length_cons]; omega)
          (by simpa only [signature,List.foldr_cons] using hchild)
        refine ⟨S,hST,?_,hSC,hSK⟩
        · exact (Finset.subset_insert j used.toFinset).trans (by simpa using hUS)
end BB336Grow

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336Cert BB336Search BB336KernelData
namespace BB336Chunk

lemma pair_chunk (anchor j : Fin 336) (hj : j ≠ anchor)
    (hc : BB336Grow.check xmask xrem xneighbors 8 [j,anchor]
      (xmask j ^^^ xmask anchor) = true)
    (v : Qubit 2 84 → ZMod 2) (ha : v (eqb anchor) ≠ 0) (hvj : v (eqb j) ≠ 0)
    (hw : weight v ≤ 10) (hv : HX polyA polyB *ᵥ v = 0) :
    ∃ u : Qubit 2 84 → ZMod 2,
      HX polyA polyB *ᵥ u = 0 ∧ u ∈ rowSpace (HZ polyA polyB) ∧
      u (eqb anchor) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0 := by
  classical
  let w := v ∘ eqb
  let T := Finset.univ.filter fun j => w j ≠ 0
  have hwi : xH *ᵥ w = 0 := by rw [← xtable]; exact index_kernel _ v hv
  have hT : ∀ i, ∑ j ∈ T, entry (xmask j) i = 0 := by
    intro i
    change ∑ j ∈ (Finset.univ.filter fun j => w j ≠ 0), xH i j = 0
    rw [← support_mul xH w i,hwi]
    rfl
  have hn : [j,anchor].Nodup := by simpa using hj
  have hu : [j,anchor].toFinset ⊆ T := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl <;> simpa [T,w] using (by assumption : v _ ≠ 0)
  have hc' : BB336Grow.check xmask xrem xneighbors 8 [j,anchor]
      (signature xmask [j,anchor]) = true := by simpa [signature] using hc
  have hweight : T.card ≤ 10 := by
    change weight (v ∘ eqb) ≤ 10
    rwa [weight_equiv]
  obtain ⟨S,hST,hAS,hSC,hSK⟩ := BB336Grow.extract xmask xrem xneighbors xones xcover T hT
    8 [j,anchor] hn hu (by simpa using hweight) hc'
  let z : Fin 336 → ZMod 2 := fun q => if q ∈ S then 1 else 0
  have hzS : (Finset.univ.filter fun q => z q ≠ 0) = S := by ext q; simp [z]
  have hzX : xH *ᵥ z = 0 := by
    ext i
    rw [support_mul,hzS]
    exact hSC i
  have hzK : xK *ᵥ z = 0 := by
    ext i
    rw [support_mul,hzS]
    exact hSK i
  have hdec : zH.transpose * xD + (1 : Matrix (Fin 336) (Fin 336) (ZMod 2)) * xK = 1 := by
    simpa only [Matrix.one_mul] using xdecomp
  have hmem := kernel_mem_row zH xD xK 1 hdec z hzK
  let u := z ∘ eqb.symm
  have hue : u ∘ eqb = z := by ext q; simp [u]
  have hux : HX polyA polyB *ᵥ u = 0 := by
    apply unindex_kernel
    rwa [xtable]
  have humem : u ∈ rowSpace (HZ polyA polyB) := by
    apply (rowspace_reindex (HZ polyA polyB) er eqb u).mp
    rwa [ztable,hue]
  have haS : anchor ∈ S := hAS (by simp)
  refine ⟨u,hux,humem,?_,?_⟩
  · simp [u,z,haS]
  · intro q hq
    have hqS : eqb.symm q ∈ S := by simpa [u,z] using hq
    have hqT := hST hqS
    simpa [T,w] using hqT
end BB336Chunk

set_option maxHeartbeats 0
open BB336Cert BB336Search
namespace BB336FastGrow

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ) :
    ℕ → List (Fin n) → BitVec r → ℕ → Bool
  | fuel, used, sy, pc =>
    if sy = 0 then decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => if 3*(fuel+1) < pc then true else (nbr (BB336High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr upd fuel (j :: used) (C j ^^^ sy) (upd j sy pc)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) (pc : ℕ) :
    check C K nbr upd fuel used sy pc =
      if sy = 0 then decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => if 3*(f+1) < pc then true else (nbr (BB336High.pick sy)).all fun j => if j ∈ used then true else
            check C K nbr upd f (j :: used) (C j ^^^ sy) (upd j sy pc) := by
  cases fuel <;> rfl

lemma step {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) (pc : ℕ) (hs : sy ≠ 0)
    (hc : ∀ j ∈ nbr (BB336High.pick sy), j ∉ used →
      check C K nbr upd fuel (j::used) (C j ^^^ sy) (upd j sy pc) = true) :
    check C K nbr upd (fuel+1) used sy pc = true := by
  rw [check_eq,if_neg hs]
  change (if 3*(fuel+1) < pc then true else (nbr (BB336High.pick sy)).all fun j =>
    if j ∈ used then true else check C K nbr upd fuel (j::used) (C j ^^^ sy) (upd j sy pc)) = true
  by_cases hp : 3*(fuel+1) < pc
  · simp only [if_pos hp]
  · rw [if_neg hp]
    apply List.all_eq_true.mpr
    intro j hj
    by_cases hu : j ∈ used
    · simp [hu]
    · simpa only [if_neg hu] using hc j hj hu

lemma sound {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (hupd : ∀ j sy, upd j sy (ones sy) = ones (C j ^^^ sy))
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r)
    (hc : check C K nbr upd fuel used sy (ones sy) = true) :
    BB336Grow.check C K nbr fuel used sy = true := by
  induction fuel generalizing used sy with
  | zero =>
    rw [BB336Grow.check_eq]
    by_cases hp : 3*0 < ones sy
    · rw [if_pos hp]
    · rw [if_neg hp]
      by_cases hz : sy = 0
      · simpa only [check_eq,if_pos hz] using hc
      · rw [if_neg hz]
  | succ f ih =>
    rw [BB336Grow.check_eq]
    by_cases hp : 3*(f+1) < ones sy
    · rw [if_pos hp]
    · rw [if_neg hp]
      rw [check_eq] at hc
      by_cases hz : sy = 0
      · rwa [if_pos hz] at *
      · rw [if_neg hz]
        rw [if_neg hz] at hc
        change (if 3*(f+1) < ones sy then true else (nbr (BB336High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr upd f (j::used) (C j ^^^ sy) (upd j sy (ones sy))) = true at hc
        rw [if_neg hp] at hc
        apply List.all_eq_true.mpr
        intro j hj
        have hh := List.all_eq_true.mp hc j hj
        by_cases hu : j ∈ used
        · simp [hu]
        · rw [if_neg hu,hupd] at hh
          simpa only [if_neg hu] using ih (j::used) (C j ^^^ sy) hh
end BB336FastGrow

open BB336Cert BB336Search BB336KernelData
namespace BB336KernelSearch
lemma anchor168_0_1_0_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [78, 79, 159, 80, 168] 182687704666362864775460756385854450003053903873 5 = true := by decide +kernel
lemma anchor168_0_1_0_2 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [167, 79, 159, 80, 168] 280608314367533360295107487882706931394656463749121 5 = true := by decide +kernel
lemma anchor168_0_1_0_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [224, 79, 159, 80, 168] 1180668181911080796161 5 = true := by decide +kernel
lemma anchor168_0_1_0_4 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [246, 79, 159, 80, 168] 20070057552195996418049 5 = true := by decide +kernel
lemma anchor168_0_1_0_5 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [250, 79, 159, 80, 168] 4836883870079234115371009 5 = true := by decide +kernel
lemma anchor168_0_1_1 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [158, 159, 80, 168] 182687704666362864775461210323332615847700070401 6 = true := by decide +kernel
lemma anchor168_0_1_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [304, 159, 80, 168] 92556803802495262667681394649472956366849 6 = true := by decide +kernel
lemma anchor168_0_1_4 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [326, 159, 80, 168] 22835963083295358176161343668957687807670747137 6 = true := by decide +kernel
lemma anchor168_0_1_5 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [330, 159, 80, 168] 5846006549323611674082390536736862908152436228097 6 = true := by decide +kernel
lemma anchor168_0_2_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [81, 160, 80, 168] 4233601551892636938272769 6 = true := by decide +kernel
lemma anchor168_0_2_2 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [161, 160, 80, 168] 2923003274661805836407370276979025570930924453889 6 = true := by decide +kernel
lemma anchor168_0_2_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [306, 160, 80, 168] 370227215209981048854975665934513228218369 6 = true := by decide +kernel
lemma anchor168_0_2_4 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [328, 160, 80, 168] 91343852333181432704643558925918087852085739521 6 = true := by decide +kernel
lemma anchor168_0_2_5 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [332, 160, 80, 168] 23384026197294446696329560331197538969231147663361 6 = true := by decide +kernel
lemma anchor168_0_3_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [58, 305, 80, 168] 10889035741470031435291329590695401881601 6 = true := by decide +kernel
lemma anchor168_0_3_1 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [137, 305, 80, 168] 98001321673230278081914797029138813157377 6 = true := by decide +kernel
lemma anchor168_0_3_2 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [138, 305, 80, 168] 359338179468511018021786495818211776266241 6 = true := by decide +kernel
lemma anchor168_0_3_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [283, 305, 80, 168] 10889079875993328981325739754349972684801 6 = true := by decide +kernel
lemma anchor168_0_3_5 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [309, 305, 80, 168] 11692015897129408903427402788985945483423822905345 6 = true := by decide +kernel
lemma anchor168_0_4_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [76, 327, 80, 168] 158457042828234071373164576769 6 = true := by decide +kernel
lemma anchor168_0_4_1 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [155, 327, 80, 168] 22835963083295358255389505076417380978641600513 6 = true := by decide +kernel
lemma anchor168_0_4_2 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [156, 327, 80, 168] 91343852333181432546187231683780123819851644929 6 = true := by decide +kernel
lemma anchor168_0_4_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [301, 327, 80, 168] 11569600475470364687246175135181798637569 6 = true := by decide +kernel
lemma anchor168_0_4_4 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [323, 327, 80, 168] 2854495385411919930477021744620514973637935105 6 = true := by decide +kernel
lemma anchor168_0_5_0_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [22, 0, 331, 80, 168] 10275869466724347987099648 3 = true := by decide +kernel
lemma anchor168_0_5_0_1 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [101, 0, 331, 80, 168] 1267660876097696125844692406272 5 = true := by decide +kernel
lemma anchor168_0_5_0_2 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [102, 0, 331, 80, 168] 5070612676782384330334802026496 5 = true := by decide +kernel
lemma anchor168_0_5_0_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [269, 0, 331, 80, 168] 10633824124745927881225856017319854080 5 = true := by decide +kernel
lemma anchor168_0_5_0_4 : BB336FastGrow.check xmask xrem xneighbors xupdate 5 [273, 0, 331, 80, 168] 170141224025298714904494875958375874560 5 = true := by decide +kernel
lemma anchor168_0_5_1 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [163, 331, 80, 168] 5846006549323611675350041154673966620410308984833 6 = true := by decide +kernel
lemma anchor168_0_5_2 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [164, 331, 80, 168] 23384026197294446693794259166158828787760080355329 6 = true := by decide +kernel
lemma anchor168_0_5_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [309, 331, 80, 168] 2961817721682383687790131951696418510471169 6 = true := by decide +kernel
lemma anchor168_0_5_5 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [335, 331, 80, 168] 187072209578355573573171779599906935974161866031105 6 = true := by decide +kernel
lemma anchor168_0_1_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [79, 159, 80, 168] 303412046524374709174273 4 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (303412046524374709174273 : BitVec 168)) = [78, 79, 167, 224, 246, 250] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor168_0_1_0_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor168_0_1_0_2
    · exact anchor168_0_1_0_3
    · exact anchor168_0_1_0_4
    · exact anchor168_0_1_0_5
lemma anchor168_0_1 : BB336FastGrow.check xmask xrem xneighbors xupdate 7 [159, 80, 168] 365375409332725729550921813822572182945985986561 5 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (365375409332725729550921813822572182945985986561 : BitVec 168)) = [79, 158, 159, 304, 326, 330] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor168_0_1_0
    · exact anchor168_0_1_1
    · exact False.elim (hju (by decide +kernel))
    · exact anchor168_0_1_3
    · exact anchor168_0_1_4
    · exact anchor168_0_1_5
lemma anchor168_0_2 : BB336FastGrow.check xmask xrem xneighbors xupdate 7 [160, 80, 168] 1461501637330902918203685439540376068405346697217 5 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (1461501637330902918203685439540376068405346697217 : BitVec 168)) = [81, 160, 161, 306, 328, 332] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor168_0_2_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor168_0_2_2
    · exact anchor168_0_2_3
    · exact anchor168_0_2_4
    · exact anchor168_0_2_5
lemma anchor168_0_3 : BB336FastGrow.check xmask xrem xneighbors xupdate 7 [305, 80, 168] 185113607604990524728538696250196498579457 5 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (185113607604990524728538696250196498579457 : BitVec 168)) = [58, 137, 138, 283, 305, 309] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor168_0_3_0
    · exact anchor168_0_3_1
    · exact anchor168_0_3_2
    · exact anchor168_0_3_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor168_0_3_5
lemma anchor168_0_4 : BB336FastGrow.check xmask xrem xneighbors xupdate 7 [327, 80, 168] 45671926166590716352322080513822326865927340033 5 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (45671926166590716352322080513822326865927340033 : BitVec 168)) = [76, 155, 156, 301, 323, 327] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor168_0_4_0
    · exact anchor168_0_4_1
    · exact anchor168_0_4_2
    · exact anchor168_0_4_3
    · exact anchor168_0_4_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor168_0_5_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 6 [0, 331, 80, 168] 2535311476325925527341395607552 4 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (2535311476325925527341395607552 : BitVec 168)) = [22, 101, 102, 269, 273, 331] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor168_0_5_0_0
    · exact anchor168_0_5_0_1
    · exact anchor168_0_5_0_2
    · exact anchor168_0_5_0_3
    · exact anchor168_0_5_0_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor168_0_5 : BB336FastGrow.check xmask xrem xneighbors xupdate 7 [331, 80, 168] 11692013098647223348164780466649632767555458301953 5 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (11692013098647223348164780466649632767555458301953 : BitVec 168)) = [0, 163, 164, 309, 331, 335] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor168_0_5_0
    · exact anchor168_0_5_1
    · exact anchor168_0_5_2
    · exact anchor168_0_5_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor168_0_5_5
lemma anchor168_0 : BB336FastGrow.check xmask xrem xneighbors xupdate 8 [80, 168] 730750818665451459101843020821051317142557818881 4 = true := by
  apply BB336FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB336High.pick (730750818665451459101843020821051317142557818881 : BitVec 168)) = [80, 159, 160, 305, 327, 331] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor168_0_1
    · exact anchor168_0_2
    · exact anchor168_0_3
    · exact anchor168_0_4
    · exact anchor168_0_5
end BB336KernelSearch
theorem bound (v : BBCode.Qubit 2 84 → ZMod 2)
    (hv : BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0,0)) ≠ 0)
    (hb : v (Sum.inl (0,80)) ≠ 0) :
    ∃ u : BBCode.Qubit 2 84 → ZMod 2,
      BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)}) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ p, u p ≠ 0 → v p ≠ 0 := by
  have h0 := hb
  have hc := BB336FastGrow.sound xmask xrem xneighbors xupdate xupdate_spec
    8 [80,168] (xmask 80 ^^^ xmask 168)
    (by rw [show (xmask 80 ^^^ xmask 168) = (730750818665451459101843020821051317142557818881 : BitVec 168) from by decide +kernel]
        simpa only [show BB336Search.ones (730750818665451459101843020821051317142557818881 : BitVec 168) = 4 from by decide +kernel] using BB336KernelSearch.anchor168_0)
  have hh := BB336Chunk.pair_chunk 168 80 (by decide +kernel) hc v
    (by simpa only [show eqb (168 : Fin 336) = (Sum.inr (0,0)) from by decide +kernel] using ha)
    (by simpa only [show eqb (80 : Fin 336) = (Sum.inl (0,80)) from by decide +kernel] using h0) hw hv
  simpa only [polyA,polyB,show eqb (168 : Fin 336) = (Sum.inr (0,0)) from by decide +kernel] using hh
end BB336Split_right_companion80

theorem solution (v : BBCode.Qubit 2 84 → ZMod 2)
    (hv : BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0,0)) ≠ 0)
    (hb : v (Sum.inl (0,80)) ≠ 0) :
    ∃ u : BBCode.Qubit 2 84 → ZMod 2,
      BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)}) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ p, u p ≠ 0 → v p ≠ 0 := BB336Split_right_companion80.bound v hv hw ha hb
#print axioms solution
