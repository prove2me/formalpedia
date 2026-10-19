-- Prove2me | solution 1 for BBCode.new336_class2_params
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:43:35.584192+00:00
-- url     : https://prove2.me/submissions/479caf89-3783-4499-8275-72b6b9399c16

import Definitions.Def_BBCode_Setting
import Theorems.Thm_BBCode_new336_class2_small_kernel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BB336C2Cert

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

end BB336C2Cert

set_option maxHeartbeats 0
open Matrix BBCode BB336C2Cert
namespace BB336C2Bits

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
end BB336C2Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336C2Cert BB336C2Bits
namespace BB336C2KernelData
def xmask (j : Fin 336) : BitVec 168 := BitVec.ofNat 168 (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 11692013098647223345629488333136821074280857993217 else 23384026197294446691258957323460528314494920687619) else (if j.val < 3 then 46768052394588893382517914646921056628989841375238 else (if j.val < 4 then 93536104789177786765035829293842113257979682750476 else 187072209578355573530071658587684226515959365500952))) else (if j.val < 7 then (if j.val < 6 then 19342813113834066795298864 else 38685626227668133590597728) else (if j.val < 8 then 77371252455336267181195456 else (if j.val < 9 then 154742504910672534362390912 else 309485009821345068724781824)))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then 618970019642690137449563648 else 1237940039285380274899127296) else (if j.val < 13 then 2475880078570760549798254592 else (if j.val < 14 then 4951760157141521099596509184 else 9903520314283042199193018368))) else (if j.val < 18 then (if j.val < 16 then 19807040628566084398386036736 else (if j.val < 17 then 39614081257132168796772073472 else 79228162514264337593544146944)) else (if j.val < 19 then 158456325028528675187088293888 else (if j.val < 20 then 316912650057057350374176587776 else 633825300114114700748353175552))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then 1267650600228229401496706351104 else 2535301200456458802993412702208) else (if j.val < 24 then 5070602400912917605986825404416 else (if j.val < 25 then 10141204801825835211973650808832 else 20282409603651670423947301617664))) else (if j.val < 28 then (if j.val < 27 then 40564819207303340847894603235328 else 81129638414606681695789206470656) else (if j.val < 29 then 162259276829213363391578412941312 else (if j.val < 30 then 324518553658426726783156825882624 else 649037107316853453566313651765248)))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then 1298074214633706907132627303530496 else 2596148429267413814265254607060992) else (if j.val < 34 then 5192296858534827628530509214121984 else (if j.val < 35 then 10384593717069655257061018428243968 else 20769187434139310514122036856487936))) else (if j.val < 39 then (if j.val < 37 then 41538374868278621028244073712975872 else (if j.val < 38 then 83076749736557242056488147425951744 else 166153499473114484112976294851903488)) else (if j.val < 40 then 332306998946228968225952589703806976 else (if j.val < 41 then 664613997892457936451905179407613952 else 1329227995784915872903810358815227904)))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then 2658455991569831745807620717630455808 else 5316911983139663491615241435260911616) else (if j.val < 45 then 10633823966279326983230482870521823232 else (if j.val < 46 then 21267647932558653966460965741043646464 else 42535295865117307932921931482087292928))) else (if j.val < 49 then (if j.val < 48 then 85070591730234615865843862964174585856 else 170141183460469231731687725928349171712) else (if j.val < 50 then 340282366920938463463375451856698343424 else (if j.val < 51 then 680564733841876926926750903713396686848 else 1361129467683753853853501807426793373696)))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then 2722258935367507707707003614853586747392 else 5444517870735015415414007229707173494784) else (if j.val < 55 then 10889035741470030830828014459414346989568 else (if j.val < 56 then 21778071482940061661656028918828693979136 else 43556142965880123323312057837657387958272))) else (if j.val < 60 then (if j.val < 58 then 87112285931760246646624115675314775916544 else (if j.val < 59 then 174224571863520493293248231350629551833088 else 348449143727040986586496462701259103666176)) else (if j.val < 61 then 696898287454081973172992925402518207332352 else (if j.val < 62 then 1393796574908163946345985850805036414664704 else 2787593149816327892691971701610072829329408))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then 5575186299632655785383943403220145658658816 else 11150372599265311570767886806440291317317632) else (if j.val < 66 then 22300745198530623141535773612880582634635264 else (if j.val < 67 then 44601490397061246283071547225761165269270528 else 89202980794122492566143094451522330538541056))) else (if j.val < 70 then (if j.val < 69 then 178405961588244985132286188903044661077082112 else 356811923176489970264572377806089322154164224) else (if j.val < 71 then 713623846352979940529144755612178644308328448 else (if j.val < 72 then 1427247692705959881058289511224357288616656896 else 2854495385411919762116579022448714577233313792)))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then 5708990770823839524233158044897429154466627584 else 11417981541647679048466316089794858308933255168) else (if j.val < 76 then 22835963083295358096932632179589716617866510336 else (if j.val < 77 then 45671926166590716193865264359179433235733020672 else 91343852333181432387730528718358866471466041344))) else (if j.val < 81 then (if j.val < 79 then 182687704666362864775461057436717732942932082688 else (if j.val < 80 then 365375409332725729550922114873435465885864165376 else 730750818665451459101844229746870931771728330752)) else (if j.val < 82 then 1461501637330902918203688459493741863543456661504 else (if j.val < 83 then 2923003274661805836407376918987483727086913323008 else 5846006549323611672814753837974967454173826646016))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then 187072209578355573530071678534960250157340748152832 else 59237365161116829560602624) else (if j.val < 87 then 118474730322233659121205248 else (if j.val < 88 then 236949460644467318242410496 else 473898921288934636484820992))) else (if j.val < 91 then (if j.val < 90 then 928455029464035206174343169 else 1856910058928070412348686338) else (if j.val < 92 then 3713820117856140824697372676 else (if j.val < 93 then 7427640235712281649394745352 else 14855280471424563298789490704)))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then 29710560942849126597578981408 else 59421121885698253195157962816) else (if j.val < 97 then 118842243771396506390315925632 else (if j.val < 98 then 237684487542793012780631851264 else 475368975085586025561263702528))) else (if j.val < 102 then (if j.val < 100 then 950737950171172051122527405056 else (if j.val < 101 then 1901475900342344102245054810112 else 3802951800684688204490109620224)) else (if j.val < 103 then 7605903601369376408980219240448 else (if j.val < 104 then 15211807202738752817960438480896 else 30423614405477505635920876961792))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then 60847228810955011271841753923584 else 121694457621910022543683507847168) else (if j.val < 108 then 243388915243820045087367015694336 else (if j.val < 109 then 486777830487640090174734031388672 else 973555660975280180349468062777344))) else (if j.val < 112 then (if j.val < 111 then 1947111321950560360698936125554688 else 3894222643901120721397872251109376) else (if j.val < 113 then 7788445287802241442795744502218752 else (if j.val < 114 then 15576890575604482885591489004437504 else 31153781151208965771182978008875008)))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then 62307562302417931542365956017750016 else 124615124604835863084731912035500032) else (if j.val < 118 then 249230249209671726169463824071000064 else (if j.val < 119 then 498460498419343452338927648142000128 else 996920996838686904677855296284000256))) else (if j.val < 123 then (if j.val < 121 then 1993841993677373809355710592568000512 else (if j.val < 122 then 3987683987354747618711421185136001024 else 7975367974709495237422842370272002048)) else (if j.val < 124 then 15950735949418990474845684740544004096 else (if j.val < 125 then 31901471898837980949691369481088008192 else 63802943797675961899382738962176016384)))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then 127605887595351923798765477924352032768 else 255211775190703847597530955848704065536) else (if j.val < 129 then 510423550381407695195061911697408131072 else (if j.val < 130 then 1020847100762815390390123823394816262144 else 2041694201525630780780247646789632524288))) else (if j.val < 133 then (if j.val < 132 then 4083388403051261561560495293579265048576 else 8166776806102523123120990587158530097152) else (if j.val < 134 then 16333553612205046246241981174317060194304 else (if j.val < 135 then 32667107224410092492483962348634120388608 else 65334214448820184984967924697268240777216)))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then 130668428897640369969935849394536481554432 else 261336857795280739939871698789072963108864) else (if j.val < 139 then 522673715590561479879743397578145926217728 else (if j.val < 140 then 1045347431181122959759486795156291852435456 else 2090694862362245919518973590312583704870912))) else (if j.val < 144 then (if j.val < 142 then 4181389724724491839037947180625167409741824 else (if j.val < 143 then 8362779449448983678075894361250334819483648 else 16725558898897967356151788722500669638967296)) else (if j.val < 145 then 33451117797795934712303577445001339277934592 else (if j.val < 146 then 66902235595591869424607154890002678555869184 else 133804471191183738849214309780005357111738368))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then 267608942382367477698428619560010714223476736 else 535217884764734955396857239120021428446953472) else (if j.val < 150 then 1070435769529469910793714478240042856893906944 else (if j.val < 151 then 2140871539058939821587428956480085713787813888 else 4281743078117879643174857912960171427575627776))) else (if j.val < 154 then (if j.val < 153 then 8563486156235759286349715825920342855151255552 else 17126972312471518572699431651840685710302511104) else (if j.val < 155 then 34253944624943037145398863303681371420605022208 else (if j.val < 156 then 68507889249886074290797726607362742841210044416 else 137015778499772148581595453214725485682420088832)))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 274031556999544297163190906429450971364840177664 else 548063113999088594326381812858901942729680355328) else (if j.val < 160 then 1096126227998177188652763625717803885459360710656 else (if j.val < 161 then 2192252455996354377305527251435607770918721421312 else 4384504911992708754611054502871215541837442842624))) else (if j.val < 165 then (if j.val < 163 then 8769009823985417509222109005742431083674885685248 else (if j.val < 164 then 17538019647970835018444218011484862167349771370496 else 35076039295941670036888436022969724334699542740992)) else (if j.val < 166 then 70152078591883340073776872045939448669399085481984 else (if j.val < 167 then 140304157183766680147553744091878897338798170963968 else 280608314367533360295107488183757794677596341927936)))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then 18446744348587458561 else 36893488697174917122) else (if j.val < 171 then 73786977394349834244 else (if j.val < 172 then 147573954788699668488 else 295147909577399336976))) else (if j.val < 175 then (if j.val < 174 then 590295819154798673952 else 1180591638309597347904) else (if j.val < 176 then 2361183276619194695808 else (if j.val < 177 then 4722366553238389391616 else 9444733106476778783232)))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then 18889466212953557566464 else 37778932425907115132928) else (if j.val < 181 then 75557864851814230265856 else (if j.val < 182 then 151115729703628460531712 else 302231459407256921063424))) else (if j.val < 186 then (if j.val < 184 then 604462918814513842126848 else (if j.val < 185 then 1208925837629027684253696 else 2417851675258055368507392)) else (if j.val < 187 then 4835703350516110737014784 else (if j.val < 188 then 9671406701032221474029568 else 288230376152760321))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then 576460752305520642 else 1152921504611041284) else (if j.val < 192 then 2305843009222082568 else (if j.val < 193 then 4611686018444165136 else 9223372036888330272))) else (if j.val < 196 then (if j.val < 195 then 18446744073776660544 else 36893488147553321088) else (if j.val < 197 then 73786976295106642176 else (if j.val < 198 then 147573952590213284352 else 295147905180426568704)))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then 590295810360853137408 else 1180591620721706274816) else (if j.val < 202 then 2361183241443412549632 else (if j.val < 203 then 4722366482886825099264 else 9444732965773650198528))) else (if j.val < 207 then (if j.val < 205 then 18889465931547300397056 else (if j.val < 206 then 37778931863094600794112 else 75557863726189201588224)) else (if j.val < 208 then 151115727452378403176448 else (if j.val < 209 then 302231454904756806352896 else 604462909809513612705792)))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then 1208925819619027225411584 else 2417851639238054450823168) else (if j.val < 213 then 4835703278476108901646336 else (if j.val < 214 then 9671406556952217803292672 else 70368811286529))) else (if j.val < 217 then (if j.val < 216 then 140737622573058 else 281475245146116) else (if j.val < 218 then 562950490292232 else (if j.val < 219 then 1125900980584464 else 2251801961168928)))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then 4503603922337856 else 9007207844675712) else (if j.val < 223 then 18014415689351424 else (if j.val < 224 then 36028831378702848 else 72057662757405696))) else (if j.val < 228 then (if j.val < 226 then 144115325514811392 else (if j.val < 227 then 288230651029622784 else 576461302059245568)) else (if j.val < 229 then 1152922604118491136 else (if j.val < 230 then 2305845208236982272 else 4611690416473964544))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then 9223380832947929088 else 18446761665895858176) else (if j.val < 234 then 36893523331791716352 else (if j.val < 235 then 73787046663583432704 else 147574093327166865408))) else (if j.val < 238 then (if j.val < 237 then 295148186654333730816 else 590296373308667461632) else (if j.val < 239 then 1180592746617334923264 else (if j.val < 240 then 2361185493234669846528 else 4722370986469339693056)))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then 9444741972938679386112 else 18889483945877358772224) else (if j.val < 244 then 37778967891754717544448 else (if j.val < 245 then 75557935783509435088896 else 151115871567018870177792))) else (if j.val < 249 then (if j.val < 247 then 302231743134037740355584 else (if j.val < 248 then 604463486268075480711168 else 1208926972536150961422336)) else (if j.val < 250 then 2417853945072301922844672 else (if j.val < 251 then 4835707890144603845689344 else 9671415780289207691378688))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then 356811928493401953423577797091436092012363776 else 713623856986803906847155594182872184024727552) else (if j.val < 255 then 1427247713973607813694311188365744368049455104 else (if j.val < 256 then 2854495427947215627388622376731488736098910208 else 5708990855894431254777244753462977472197820416))) else (if j.val < 259 then (if j.val < 258 then 11417981711788862509554489506925954944395640832 else 22835963423577725019108979013851909888791281664) else (if j.val < 260 then 45671926847155450038217958027703819777582563328 else (if j.val < 261 then 91343853694310900076435916055407639555165126656 else 182687707388621800152871832110815279110330253312)))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then 365375414777243600305743664221630558220660506624 else 730750829554487200611487328443261116441321013248) else (if j.val < 265 then 1461501659108974401222974656886522232882642026496 else (if j.val < 266 then 2923003318217948802445949313773044465765284052992 else 5846006636435897604891898627546088931530568105984))) else (if j.val < 270 then (if j.val < 268 then 11692013272871795209783797255092177863061136211968 else (if j.val < 269 then 23384026545743590419567594510184355726122272423936 else 46768053091487180839135189020368711452244544847872)) else (if j.val < 271 then 93536106182974361678270378040737422904489089695744 else (if j.val < 272 then 187072212365948723356540756081474845808978179391488 else 5575186299652938214330394352420104423079936))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then 11150372599305876428660788704840208846159872 else 22300745198611752857321577409680417692319744) else (if j.val < 276 then 44601490397223505714643154819360835384639488 else (if j.val < 277 then 89202980794447011429286309638721670769278976 else 178405961588894022858572619277443341538557952))) else (if j.val < 280 then (if j.val < 279 then 356811923177788045717145238554886683077115904 else 713623846355576091434290477109773366154231808) else (if j.val < 281 then 1427247692711152182868580954219546732308463616 else (if j.val < 282 then 2854495385422304365737161908439093464616927232 else 5708990770844608731474323816878186929233854464)))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then 11417981541689217462948647633756373858467708928 else 22835963083378434925897295267512747716935417856) else (if j.val < 286 then 45671926166756869851794590535025495433870835712 else (if j.val < 287 then 91343852333513739703589181070050990867741671424 else 182687704667027479407178362140101981735483342848))) else (if j.val < 291 then (if j.val < 289 then 365375409334054958814356724280203963470966685696 else (if j.val < 290 then 730750818668109917628713448560407926941933371392 else 1461501637336219835257426897120815853883866742784)) else (if j.val < 292 then 2923003274672439670514853794241631707767733485568 else (if j.val < 293 then 5846006549344879341029707588483263415535466971136 else 11692013098689758682059415176966526831070933942272)))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then 23384026197379517364118830353933053662141867884544 else 46768052394759034728237660707866107324283735769088) else (if j.val < 297 then 93536104789518069456475321415732214648567471538176 else (if j.val < 298 then 187072209579036138912950642831464429297134943076352 else 1361130765757987830373519396417950449664))) else (if j.val < 301 then (if j.val < 300 then 2722261531515975660747038792835900899328 else 5444523063031951321494077585671801798656) else (if j.val < 302 then 10889046126063902642988155171343603597312 else (if j.val < 303 then 21778092252127805285976310342687207194624 else 43556184504255610571952620685374414389248)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then 87112369008511221143905241370748828778496 else 174224738017022442287810482741497657556992) else (if j.val < 307 then 348449476034044884575620965482995315113984 else (if j.val < 308 then 696898952068089769151241930965990630227968 else 1393797904136179538302483861931981260455936))) else (if j.val < 312 then (if j.val < 310 then 2787595808272359076604967723863962520911872 else (if j.val < 311 then 5575191616544718153209935447727925041823744 else 11150383233089436306419870895455850083647488)) else (if j.val < 313 then 22300766466178872612839741790911700167294976 else (if j.val < 314 then 44601532932357745225679483581823400334589952 else 89203065864715490451358967163646800669179904))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 178406131729430980902717934327293601338359808 else 356812263458861961805435868654587202676719616) else (if j.val < 318 then 713624526917723923610871737309174405353439232 else (if j.val < 319 then 1427249053835447847221743474618348810706878464 else 2854498107670895694443486949236697621413756928))) else (if j.val < 322 then (if j.val < 321 then 5708996215341791388886973898473395242827513856 else 11417992430683582777773947796946790485655027712) else (if j.val < 323 then 22835984861367165555547895593893580971310055424 else (if j.val < 324 then 45671969722734331111095791187787161942620110848 else 91343939445468662222191582375574323885240221696)))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then 182687878890937324444383164751148647770480443392 else 365375757781874648888766329502297295540960886784) else (if j.val < 328 then 730751515563749297777532659004594591081921773568 else (if j.val < 329 then 1461503031127498595555065318009189182163843547136 else 2923006062254997191110130636018378364327687094272))) else (if j.val < 333 then (if j.val < 331 then 5846012124509994382220261272036756728655374188544 else (if j.val < 332 then 11692024249019988764440522544073513457310748377088 else 23384048498039977528881045088147026914621496754176)) else (if j.val < 334 then 46768096996079955057762090176294053829242993508352 else (if j.val < 335 then 93536193992159910115524180352588107658485987016704 else 187072387984319820231048360705176215316971974033408)))))))))
def xrow (i : Fin 168) : BitVec 336 := BitVec.ofNat 336 (if i.val < 84 then (if i.val < 42 then (if i.val < 21 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 26328073309458529280566211371801507174139070244630215148760465411 else 52656146618917058561132422743603014348278140489260430297520930822) else (if i.val < 3 then 105312293237834117122264845487206028696556280978520860595041861644 else (if i.val < 4 then 210624586475668234244529690974412057393112561957041721190083723288 else 421249172951336468489059381948824114786225123914083442380167446576))) else (if i.val < 7 then (if i.val < 6 then 842498345902672936978118763897648229572450247828166884760334893152 else 1684996691805345873956237527795296459144900495656333769520669786304) else (if i.val < 8 then 3369993383610691747912475055590592918289800991312667539041339572608 else (if i.val < 9 then 6739986767221383495824950111181185836579601982625335078082679145216 else 13479973534442766991649900222362371673159203965250670156165358290432)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 26959947068885533983299800444724743346318407930501340312330716580864 else 53919894137771067966599600889449486692636815861002680624661433161728) else (if i.val < 13 then 107839788275542135933199201778898973385273631722005361249322866323456 else (if i.val < 14 then 215679576551084271866398403557797946770547263444010722498645732646912 else 431359153102168543732796807115595893541094526888021444997291465293824))) else (if i.val < 18 then (if i.val < 16 then 862718306204337087465593614231191787082189053776042889994582930587648 else (if i.val < 17 then 1725436612408674174931187228462383574164378107552085779989165861175296 else 3450873224817348349862374456924767148328756215104171559978331722350592)) else (if i.val < 19 then 6901746449634696699724748913849534296657512430208343119956663444701184 else (if i.val < 20 then 13803492899269393399449497827699068593315024860416686239913326889402368 else 27606985798538786798898995655398137186630049720833372479826653778804736))))) else (if i.val < 31 then (if i.val < 26 then (if i.val < 23 then (if i.val < 22 then 55213971597077573597797991310796274373260099441666744959653307557609472 else 110427943194155147195595982621592548746520198883333489919306615115218944) else (if i.val < 24 then 220855886388310294391191965243185097493040397766666979838613230230437888 else (if i.val < 25 then 441711772776620588782383930486370194986080795533333959677226460460875776 else 883423545553241177564767860972740389972161591066667919354452920921751552))) else (if i.val < 28 then (if i.val < 27 then 1766847091106482355129535721945480779944323182133335838708905841843503104 else 3533694182212964710259071443890961559888646364266671677417811683687006208) else (if i.val < 29 then 7067388364425929420518142887781923119777292728533343354835623367374012416 else (if i.val < 30 then 14134776728851858841036285775563846239554585457066686709671246734748024832 else 28269553457703717682072571551127692479109170914133373419342493469496049664)))) else (if i.val < 36 then (if i.val < 33 then (if i.val < 32 then 56539106915407435364145143102255384958218341828266746838684986938992099328 else 113078213830814870728290286204510769916436683656533493677369973877984198656) else (if i.val < 34 then 226156427661629741456580572409021539832873367313066987354739947755968397312 else (if i.val < 35 then 452312855323259482913161144818043079665746734626133974709479895511936794624 else 904625710646518965826322289636086159331493469252267949418959791023873589248))) else (if i.val < 39 then (if i.val < 37 then 1809251421293037931652644579272172318662986938504535898837919582047747178496 else (if i.val < 38 then 3618502842586075863305289158544344637325973877009071797675839164095494356992 else 107839889512637392128190114190533720772558925518254032359615149113344)) else (if i.val < 40 then 215679779025274784256380228381067441545117851036508064719230298226688 else (if i.val < 41 then 431359558050549568512760456762134883090235702073016129438460596453376 else 862719116101099137025520913524269766180471404146032258876921192906752)))))) else (if i.val < 63 then (if i.val < 52 then (if i.val < 47 then (if i.val < 44 then (if i.val < 43 then 1725438232202198274051041827048539532360942808292064517753842385813504 else 3450876464404396548102083654097079064721885616584129035507684771627008) else (if i.val < 45 then 6901752928808793096204167308194158129443771233168258071015369543254016 else (if i.val < 46 then 13803505857617586192408334616388316258887542466336516142030739086508032 else 27607011715235172384816669232776632517775084932673032284061478173016064))) else (if i.val < 49 then (if i.val < 48 then 55214023430470344769633338465553265035550169865346064568122956346032128 else 110428046860940689539266676931106530071100339730692129136245912692064256) else (if i.val < 50 then 220856093721881379078533353862213060142200679461384258272491825384128512 else (if i.val < 51 then 441712187443762758157066707724426120284401358922768516544983650768257024 else 883424374887525516314133415448852240568802717845537033089967301536514048)))) else (if i.val < 57 then (if i.val < 54 then (if i.val < 53 then 1766848749775051032628266830897704481137605435691074066179934603073028096 else 3533697499550102065256533661795408962275210871382148132359869206146056192) else (if i.val < 55 then 7067394999100204130513067323590817924550421742764296264719738412292112384 else (if i.val < 56 then 14134789998200408261026134647181635849100843485528592529439476824584224768 else 28269579996400816522052269294363271698201686971057185058878953649168449536))) else (if i.val < 60 then (if i.val < 58 then 56539159992801633044104538588726543396403373942114370117757907298336899072 else (if i.val < 59 then 113078319985603266088209077177453086792806747884228740235515814596673798144 else 226156639971206532176418154354906173585613495768457480471031629193347596288)) else (if i.val < 61 then 452313279942413064352836308709812347171226991536914960942063258386695192576 else (if i.val < 62 then 904626559884826128705672617419624694342453983073829921884126516773390385152 else 1809253119769652257411345234839249388684907966147659843768253033546780770304))))) else (if i.val < 73 then (if i.val < 68 then (if i.val < 65 then (if i.val < 64 then 3618506239539304514822690469678498777369815932295319687536506067093561540608 else 6901746346815672194750458422470621404883131421297975366165611283480576) else (if i.val < 66 then 13803492693631344389500916844941242809766262842595950732331222566961152 else (if i.val < 67 then 27606985387262688779001833689882485619532525685191901464662445133922304 else 55213970774525377558003667379764971239065051370383802929324890267844608))) else (if i.val < 70 then (if i.val < 69 then 110427941549050755116007334759529942478130102740767605858649780535689216 else 220855883098101510232014669519059884956260205481535211717299561071378432) else (if i.val < 71 then 441711766196203020464029339038119769912520410963070423434599122142756864 else (if i.val < 72 then 883423532392406040928058678076239539825040821926140846869198244285513728 else 1766847064784812081856117356152479079650081643852281693738396488571027456)))) else (if i.val < 78 then (if i.val < 75 then (if i.val < 74 then 3533694129569624163712234712304958159300163287704563387476792977142054912 else 7067388259139248327424469424609916318600326575409126774953585954284109824) else (if i.val < 76 then 14134776518278496654848938849219832637200653150818253549907171908568219648 else (if i.val < 77 then 28269553036556993309697877698439665274401306301636507099814343817136439296 else 56539106073113986619395755396879330548802612603273014199628687634272878592))) else (if i.val < 81 then (if i.val < 79 then 113078212146227973238791510793758661097605225206546028399257375268545757184 else (if i.val < 80 then 226156424292455946477582647443098165484063390269794224243175552685155811328 else 452312848584911892955165294886196330968126780539588448486351105370311622656)) else (if i.val < 82 then 904625697169823785910330589772392661936253561079176896972702210740623245312 else (if i.val < 83 then 1809251394339647571820661179544785323872507122158353793945404421481246490624 else 3618502788679295143641322359089570647745014244316688245077695008895697682433))))))) else (if i.val < 126 then (if i.val < 105 then (if i.val < 94 then (if i.val < 89 then (if i.val < 86 then (if i.val < 85 then 509259001672179118829442937643706586978800870482626607080496719821768455923931735585194016 else 1018518003344358237658885875287413173957601740965253214160993439643536911847863471170388032) else (if i.val < 87 then 2037036006688716475317771750574826347915203481930506428321986879287073823695726942340776064 else (if i.val < 88 then 4074072013377432950635543501149652695830406963861012856643973758574147647391453884681552128 else 8148144026754865901271087002299305391660813927722025713287947517148295294782907769363104256))) else (if i.val < 91 then (if i.val < 90 then 16296288053509731802542174004598610783321627855444051426575895034296590589565815538726208512 else 32592576107019463605084348009197221566643255710888102853151790068593181179131631077452417024) else (if i.val < 92 then 65185152214038927210168696018394443133286511421776205706303580137186362358263262154904834048 else (if i.val < 93 then 130370304428077854420337392036788886266573022843552411412607160274372724716526524309809668096 else 260740608856155708840674784073577772533146045687104822825214320548745449433053048619619336192)))) else (if i.val < 99 then (if i.val < 96 then (if i.val < 95 then 521481217712311417681349568147155545066292091374209645650428641097490898866106097239238672384 else 1042962435424622835362699136294311090132584182748419291300857282194981797732212194478477344768) else (if i.val < 97 then 2085924870849245670725398272588622180265168365496838582601714564389963595464424388956954689536 else (if i.val < 98 then 4171849741698491341450796545177244360530336730993677165203429128779927190928848777913909379072 else 8343699483396982682901593090354488721060673461987354330406858257559854381857697555827818758144))) else (if i.val < 102 then (if i.val < 100 then 16687398966793965365803186180708977442121346923974708660813716515119708763715395111655637516288 else (if i.val < 101 then 33374797933587930731606372361417954884242693847949417321627433030239417527430790223311275032576 else 66749595867175861463212744722835909768485387695898834643254866060478835054861580446622550065152)) else (if i.val < 103 then 133499191734351722926425489445671819536970775391797669286509732120957670109723160893245100130304 else (if i.val < 104 then 266998383468703445852850978891343639073941550783595338573019464241915340219446321786490200260608 else 533996766937406891705701957782687278147883101567190677146038928483830680438892643572980400521216))))) else (if i.val < 115 then (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then 1067993533874813783411403915565374556295766203134381354292077856967661360877785287145960801042432 else 2135987067749627566822807831130749112591532406268762708584155713935322721755570574291921602084864) else (if i.val < 108 then 4271974135499255133645615662261498225183064812537525417168311427870645443511141148583843204169728 else (if i.val < 109 then 8543948270998510267291231324522996450366129625075050834336622855741290887022282297167686408339456 else 17087896541997020534582462649045992900732259250150101668673245711482581774044564594335372816678912))) else (if i.val < 112 then (if i.val < 111 then 34175793083994041069164925298091985801464518500300203337346491422965163548089129188670745633357824 else 68351586167988082138329850596183971602929037000600406674692982845930327096178258377341491266715648) else (if i.val < 113 then 136703172335976164276659701192367943205858074001200813349385965691860654192356516754682982533431296 else (if i.val < 114 then 273406344671952328553319402384735886411716148002401626698771931383721308384713033509365965066862592 else 546812689343904657106638804769471772823432296004803253397543862767442616769426067018731930133725184)))) else (if i.val < 120 then (if i.val < 117 then (if i.val < 116 then 1093625378687809314213277609538943545646864592009606506795087725534885233538852134037463860267450368 else 2187250757375618628426555219077887091293729184019213013590175451069770467077704268074927720534900736) else (if i.val < 118 then 4374501514751237256853110438155774182587458368038426027180350902139540934155408536149855441069801472 else (if i.val < 119 then 8749003029502474513706220876311548365174916736076852054360701804279081868310817072299710882139602944 else 17498006059004949027412441752623096730349833472153704108721403608558163736621634144599421764279205888))) else (if i.val < 123 then (if i.val < 121 then 34996012118009898054824883505246193460699666944307408217442807217116327473243268289198843528558411776 else (if i.val < 122 then 69992024236019796109649767010492386921399333888614816434885614434232654946486536578397687057116823552 else 2085926829059459398722462583792458038173250599981516150887602359546748266536589531279328804864)) else (if i.val < 124 then 4171853658118918797444925167584916076346501199963032301775204719093496533073179062558657609728 else (if i.val < 125 then 8343707316237837594889850335169832152693002399926064603550409438186993066146358125117315219456 else 16687414632475675189779700670339664305386004799852129207100818876373986132292716250234630438912)))))) else (if i.val < 147 then (if i.val < 136 then (if i.val < 131 then (if i.val < 128 then (if i.val < 127 then 33374829264951350379559401340679328610772009599704258414201637752747972264585432500469260877824 else 66749658529902700759118802681358657221544019199408516828403275505495944529170865000938521755648) else (if i.val < 129 then 133499317059805401518237605362717314443088038398817033656806551010991889058341730001877043511296 else (if i.val < 130 then 266998634119610803036475210725434628886176076797634067313613102021983778116683460003754087022592 else 533997268239221606072950421450869257772352153595268134627226204043967556233366920007508174045184))) else (if i.val < 133 then (if i.val < 132 then 1067994536478443212145900842901738515544704307190536269254452408087935112466733840015016348090368 else 2135989072956886424291801685803477031089408614381072538508904816175870224933467680030032696180736) else (if i.val < 134 then 4271978145913772848583603371606954062178817228762145077017809632351740449866935360060065392361472 else (if i.val < 135 then 8543956291827545697167206743213908124357634457524290154035619264703480899733870720120130784722944 else 17087912583655091394334413486427816248715268915048580308071238529406961799467741440240261569445888)))) else (if i.val < 141 then (if i.val < 138 then (if i.val < 137 then 34175825167310182788668826972855632497430537830097160616142477058813923598935482880480523138891776 else 68351650334620365577337653945711264994861075660194321232284954117627847197870965760961046277783552) else (if i.val < 139 then 136703300669240731154675307891422529989722151320388642464569908235255694395741931521922092555567104 else (if i.val < 140 then 273406601338481462309350615782845059979444302640777284929139816470511388791483863043844185111134208 else 546813202676962924618701231565690119958888605281554569858279632941022777582967726087688370222268416))) else (if i.val < 144 then (if i.val < 142 then 1093626405353925849237402463131380239917777210563109139716559265882045555165935452175376740444536832 else (if i.val < 143 then 2187252810707851698474804926262760479835554421126218279433118531764091110331870904350753480889073664 else 4374505621415703396949609852525520959671108842252436558866237063528182220663741808701506961778147328)) else (if i.val < 145 then 8749011242831406793899219705051041919342217684504873117732474127056364441327483617403013923556294656 else (if i.val < 146 then 17498022485662813587798439410102083838684435369009746235464948254112728882654967234806027847112589312 else 34996044971325627175596878820204167677368870738019492470929896508225457765309934469612055694225178624))))) else (if i.val < 157 then (if i.val < 152 then (if i.val < 149 then (if i.val < 148 then 69992089942651254351193757640408335354737741476038984941859793016450915530619868939224111388450357248 else 133499189745542547379982294480659134853348098936995464508052038880715014931258242379941995872256) else (if i.val < 150 then 266998379491085094759964588961318269706696197873990929016104077761430029862516484759883991744512 else (if i.val < 151 then 533996758982170189519929177922636539413392395747981858032208155522860059725032969519767983489024 else 1067993517964340379039858355845273078826784791495963716064416311045720119450065939039535966978048))) else (if i.val < 154 then (if i.val < 153 then 2135987035928680758079716711690546157653569582991927432128832622091440238900131878079071933956096 else 4271974071857361516159433423381092315307139165983854864257665244182880477800263756158143867912192) else (if i.val < 155 then 8543948143714723032318866846762184630614278331967709728515330488365760955600527512316287735824384 else (if i.val < 156 then 17087896287429446064637733693524369261228556663935419457030660976731521911201055024632575471648768 else 34175792574858892129275467387048738522457113327870838914061321953463043822402110049265150943297536)))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then 68351585149717784258550934774097477044914226655741677828122643906926087644804220098530301886595072 else 136703170299435568517101869548194954089828453311483355656245287813852175289608440197060603773190144) else (if i.val < 160 then 273406340598871137034203739096389908179656906622966711312490575627704350579216880394121207546380288 else (if i.val < 161 then 546812681197742274068407478192779816359313813245933422624981151255408701158433760788242415092760576 else 1093625362395484548136814956385559632718627626491866845249962302510817402316867521576484830185521152))) else (if i.val < 165 then (if i.val < 163 then 2187250724790969096273629912771119265437255252983733690499924605021634804633735043152969660371042304 else (if i.val < 164 then 4374501449581938192547259825542238530874510505967467380999849210043269609248127273192105253946785793 else 8749002899163876385094519651084477061749021011934934761999698420086539218496254546384210507893571586)) else (if i.val < 166 then 17498005798327752770189039302168954123498042023869869523999396840173078436992509092768421015787143172 else (if i.val < 167 then 34996011596655505540378078604337908246996084047739739047998793680346156873985018185536842031574286344 else 69992023193311011080756157208675816493992168095479103951578430649545253604672203815734486211212869648))))))))
def xH : Matrix (Fin 168) (Fin 336) (ZMod 2) := fun i j => entry (xmask j) i
def zmask (j : Fin 336) : BitVec 168 := BitVec.ofNat 168 (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 70368745226241 else 140737490452482) else (if j.val < 3 then 281474980904964 else (if j.val < 4 then 562949961809928 else 1125899923619856))) else (if j.val < 7 then (if j.val < 6 then 2251799847239712 else 4503599694479424) else (if j.val < 8 then 9007199388958848 else (if j.val < 9 then 18014398777917696 else 36028797555835392)))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then 72057595111670784 else 144115190223341568) else (if j.val < 13 then 288230380446683136 else (if j.val < 14 then 576460760893366272 else 1152921521786732544))) else (if j.val < 18 then (if j.val < 16 then 2305843043573465088 else (if j.val < 17 then 4611686087146930176 else 9223372174293860352)) else (if j.val < 19 then 18446744348587720704 else (if j.val < 20 then 36893488697175441408 else 73786977394350882816))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then 147573954788701765632 else 295147909577403531264) else (if j.val < 24 then 590295819154807062528 else (if j.val < 25 then 1180591638309614125056 else 2361183276619228250112))) else (if j.val < 28 then (if j.val < 27 then 4722366553238456500224 else 9444733106476913000448) else (if j.val < 29 then 18889466212953826000896 else (if j.val < 30 then 37778932425907652001792 else 75557864851815304003584)))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then 151115729703630608007168 else 302231459407261216014336) else (if j.val < 34 then 604462918814522432028672 else (if j.val < 35 then 1208925837629044864057344 else 2417851675258089728114688))) else (if j.val < 39 then (if j.val < 37 then 4835703350516179456229376 else (if j.val < 38 then 9671406701032358912458752 else 288230651029618689)) else (if j.val < 40 then 576461302059237378 else (if j.val < 41 then 1152922604118474756 else 2305845208236949512)))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then 4611690416473899024 else 9223380832947798048) else (if j.val < 45 then 18446761665895596096 else (if j.val < 46 then 36893523331791192192 else 73787046663582384384))) else (if j.val < 49 then (if j.val < 48 then 147574093327164768768 else 295148186654329537536) else (if j.val < 50 then 590296373308659075072 else (if j.val < 51 then 1180592746617318150144 else 2361185493234636300288)))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then 4722370986469272600576 else 9444741972938545201152) else (if j.val < 55 then 18889483945877090402304 else (if j.val < 56 then 37778967891754180804608 else 75557935783508361609216))) else (if j.val < 60 then (if j.val < 58 then 151115871567016723218432 else (if j.val < 59 then 302231743134033446436864 else 604463486268066892873728)) else (if j.val < 61 then 1208926972536133785747456 else (if j.val < 62 then 2417853945072267571494912 else 4835707890144535142989824))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then 9671415780289070285979648 else 18446744073776660481) else (if j.val < 66 then 36893488147553320962 else (if j.val < 67 then 73786976295106641924 else 147573952590213283848))) else (if j.val < 70 then (if j.val < 69 then 295147905180426567696 else 590295810360853135392) else (if j.val < 71 then 1180591620721706270784 else (if j.val < 72 then 2361183241443412541568 else 4722366482886825083136)))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then 9444732965773650166272 else 18889465931547300332544) else (if j.val < 76 then 37778931863094600665088 else (if j.val < 77 then 75557863726189201330176 else 151115727452378402660352))) else (if j.val < 81 then (if j.val < 79 then 302231454904756805320704 else (if j.val < 80 then 604462909809513610641408 else 1208925819619027221282816)) else (if j.val < 82 then 2417851639238054442565632 else (if j.val < 83 then 4835703278476108885131264 else 9671406556952217770262528))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then 1361129487966182800318282687741119430656 else 2722258975932365600636565375482238861312) else (if j.val < 87 then 5444517951864731201273130750964477722624 else (if j.val < 88 then 10889035903729462402546261501928955445248 else 21778071807458924805092523003857910890496))) else (if j.val < 91 then (if j.val < 90 then 43556143614917849610185046007715821780992 else 87112287229835699220370092015431643561984) else (if j.val < 92 then 174224574459671398440740184030863287123968 else (if j.val < 93 then 348449148919342796881480368061726574247936 else 696898297838685593762960736123453148495872)))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then 1393796595677371187525921472246906296991744 else 2787593191354742375051842944493812593983488) else (if j.val < 97 then 5575186382709484750103685888987625187966976 else (if j.val < 98 then 11150372765418969500207371777975250375933952 else 22300745530837939000414743555950500751867904))) else (if j.val < 102 then (if j.val < 100 then 44601491061675878000829487111901001503735808 else (if j.val < 101 then 89202982123351756001658974223802003007471616 else 178405964246703512003317948447604006014943232)) else (if j.val < 103 then 356811928493407024006635896895208012029886464 else (if j.val < 104 then 713623856986814048013271793790416024059772928 else 1427247713973628096026543587580832048119545856))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then 2854495427947256192053087175161664096239091712 else 5708990855894512384106174350323328192478183424) else (if j.val < 108 then 11417981711789024768212348700646656384956366848 else (if j.val < 109 then 22835963423578049536424697401293312769912733696 else 45671926847156099072849394802586625539825467392))) else (if j.val < 112 then (if j.val < 111 then 91343853694312198145698789605173251079650934784 else 182687707388624396291397579210346502159301869568) else (if j.val < 113 then 365375414777248792582795158420693004318603739136 else (if j.val < 114 then 730750829554497585165590316841386008637207478272 else 1461501659108995170331180633682772017274414956544)))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then 2923003318217990340662361267365544034548829913088 else 5846006636435980681324722534731088069097659826176) else (if j.val < 118 then 11692013272871961362649445069462176138195319652352 else (if j.val < 119 then 23384026545743922725298890138924352276390639304704 else 46768053091487845450597780277848704552781278609408))) else (if j.val < 123 then (if j.val < 121 then 93536106182975690901195560555697409105562557218816 else (if j.val < 122 then 187072212365951381802391121111394818211125114437632 else 5575191616544638944390234297224398293172224)) else (if j.val < 124 then 11150383233089277888780468594448796586344448 else (if j.val < 125 then 22300766466178555777560937188897593172688896 else 44601532932357111555121874377795186345377792)))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then 89203065864714223110243748755590372690755584 else 178406131729428446220487497511180745381511168) else (if j.val < 129 then 356812263458856892440974995022361490763022336 else (if j.val < 130 then 713624526917713784881949990044722981526044672 else 1427249053835427569763899980089445963052089344))) else (if j.val < 133 then (if j.val < 132 then 2854498107670855139527799960178891926104178688 else 5708996215341710279055599920357783852208357376) else (if j.val < 134 then 11417992430683420558111199840715567704416714752 else (if j.val < 135 then 22835984861366841116222399681431135408833429504 else 45671969722733682232444799362862270817666859008)))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then 91343939445467364464889598725724541635333718016 else 182687878890934728929779197451449083270667436032) else (if j.val < 139 then 365375757781869457859558394902898166541334872064 else (if j.val < 140 then 730751515563738915719116789805796333082669744128 else 1461503031127477831438233579611592666165339488256))) else (if j.val < 144 then (if j.val < 142 then 2923006062254955662876467159223185332330678976512 else (if j.val < 143 then 5846012124509911325752934318446370664661357953024 else 11692024249019822651505868636892741329322715906048)) else (if j.val < 145 then 23384048498039645303011737273785482658645431812096 else (if j.val < 146 then 46768096996079290606023474547570965317290863624192 else 93536193992158581212046949095141930634581727248384))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then 187072387984317162424093898190283861269163454496768 else 356811923177788044498548012383340474973290496) else (if j.val < 150 then 713623846355576088997096024766680949946580992 else (if j.val < 151 then 1427247692711152177994192049533361899893161984 else 2854495385422304355988384099066723799786323968))) else (if j.val < 154 then (if j.val < 153 then 5708990770844608711976768198133447599572647936 else 11417981541689217423953536396266895199145295872) else (if j.val < 155 then 22835963083378434847907072792533790398290591744 else (if j.val < 156 then 45671926166756869695814145585067580796581183488 else 91343852333513739391628291170135161593162366976)))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 182687704667027478783256582340270323186324733952 else 365375409334054957566513164680540646372649467904) else (if j.val < 160 then 730750818668109915133026329361081292745298935808 else (if j.val < 161 then 1461501637336219830266052658722162585490597871616 else 2923003274672439660532105317444325170981195743232))) else (if j.val < 165 then (if j.val < 163 then 5846006549344879321064210634888650341962391486464 else (if j.val < 164 then 11692013098689758642128421269777300683924782972928 else 23384026197379517284256842539554601367849565945856)) else (if j.val < 166 then 46768052394759034568513685079109202735699131891712 else (if j.val < 167 then 93536104789518069137027370158218405471398263783424 else 187072209579036138274054740316436810942796527566848)))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then 618970019642690137449562115 else 1237940039285380274899124230) else (if j.val < 171 then 2475880078570760549798248460 else (if j.val < 172 then 4951760157141521099596496920 else 9903520314283042199192993840))) else (if j.val < 175 then (if j.val < 174 then 19807040628566084398385987680 else 39614081257132168796771975360) else (if j.val < 176 then 79228162514264337593543950720 else (if j.val < 177 then 158456325028528675187087901440 else 316912650057057350374175802880)))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then 633825300114114700748351605760 else 1267650600228229401496703211520) else (if j.val < 181 then 2535301200456458802993406423040 else (if j.val < 182 then 5070602400912917605986812846080 else 10141204801825835211973625692160))) else (if j.val < 186 then (if j.val < 184 then 20282409603651670423947251384320 else (if j.val < 185 then 40564819207303340847894502768640 else 81129638414606681695789005537280)) else (if j.val < 187 then 162259276829213363391578011074560 else (if j.val < 188 then 324518553658426726783156022149120 else 649037107316853453566312044298240))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then 1298074214633706907132624088596480 else 2596148429267413814265248177192960) else (if j.val < 192 then 5192296858534827628530496354385920 else (if j.val < 193 then 10384593717069655257060992708771840 else 20769187434139310514121985417543680))) else (if j.val < 196 then (if j.val < 195 then 41538374868278621028243970835087360 else 83076749736557242056487941670174720) else (if j.val < 197 then 166153499473114484112975883340349440 else (if j.val < 198 then 332306998946228968225951766680698880 else 664613997892457936451903533361397760)))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then 1329227995784915872903807066722795520 else 2658455991569831745807614133445591040) else (if j.val < 202 then 5316911983139663491615228266891182080 else (if j.val < 203 then 10633823966279326983230456533782364160 else 21267647932558653966460913067564728320))) else (if j.val < 207 then (if j.val < 205 then 42535295865117307932921826135129456640 else (if j.val < 206 then 85070591730234615865843652270258913280 else 170141183460469231731687304540517826560)) else (if j.val < 208 then 340282366920938463463374609081035653120 else (if j.val < 209 then 680564733841876926926749218162071306240 else 1361129467683753853853498436324142612480)))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then 2722258935367507707706996872648285224960 else 5444517870735015415413993745296570449920) else (if j.val < 213 then 10889035741470030830827987490593140899840 else (if j.val < 214 then 21778071482940061661655974981186281799680 else 43556142965880123323311949962372563599360))) else (if j.val < 217 then (if j.val < 216 then 87112285931760246646623899924745127198720 else 174224571863520493293247799849490254397440) else (if j.val < 218 then 348449143727040986586495599698980508794880 else (if j.val < 219 then 696898287454081973172991199397961017589760 else 1393796574908163946345982398795922035179520)))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then 2787593149816327892691964797591844070359040 else 5575186299632655785383929595183688140718080) else (if j.val < 223 then 11150372599265311570767859190367376281436160 else (if j.val < 224 then 22300745198530623141535718380734752562872320 else 44601490397061246283071436761469505125744640))) else (if j.val < 228 then (if j.val < 226 then 89202980794122492566142873522939010251489280 else (if j.val < 227 then 178405961588244985132285747045878020502978560 else 356811923176489970264571494091756041005957120)) else (if j.val < 229 then 713623846352979940529142988183512082011914240 else (if j.val < 230 then 1427247692705959881058285976367024164023828480 else 2854495385411919762116571952734048328047656960))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then 5708990770823839524233143905468096656095313920 else 11417981541647679048466287810936193312190627840) else (if j.val < 234 then 22835963083295358096932575621872386624381255680 else (if j.val < 235 then 45671926166590716193865151243744773248762511360 else 91343852333181432387730302487489546497525022720))) else (if j.val < 238 then (if j.val < 237 then 182687704666362864775460604974979092995050045440 else 365375409332725729550921209949958185990100090880) else (if j.val < 239 then 730750818665451459101842419899916371980200181760 else (if j.val < 240 then 1461501637330902918203684839799832743960400363520 else 2923003274661805836407369679599665487920800727040)))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then 5846006549323611672814739359199330975841601454080 else 11692013098647223345629478718398661951683202908160) else (if j.val < 244 then 23384026197294446691258957436797323903366405816320 else (if j.val < 245 then 46768052394588893382517914873594647806732811632640 else 93536104789177786765035829747189295613465623265280))) else (if j.val < 249 then (if j.val < 247 then 187072209578355573530071659494378591226931246530560 else (if j.val < 248 then 21156201843256010557358080 else 42312403686512021114716160)) else (if j.val < 250 then 84624807373024042229432320 else (if j.val < 251 then 169249614746048084458864640 else 319156416378262102122430465))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then 58028439341502200385896480 else 116056878683004400771792960) else (if j.val < 255 then 232113757366008801543585920 else (if j.val < 256 then 464227514732017603087171840 else 928455029464035206174343680))) else (if j.val < 259 then (if j.val < 258 then 1856910058928070412348687360 else 3713820117856140824697374720) else (if j.val < 260 then 7427640235712281649394749440 else (if j.val < 261 then 14855280471424563298789498880 else 29710560942849126597578997760)))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then 59421121885698253195157995520 else 118842243771396506390315991040) else (if j.val < 265 then 237684487542793012780631982080 else (if j.val < 266 then 475368975085586025561263964160 else 950737950171172051122527928320))) else (if j.val < 270 then (if j.val < 268 then 1901475900342344102245055856640 else (if j.val < 269 then 3802951800684688204490111713280 else 7605903601369376408980223426560)) else (if j.val < 271 then 15211807202738752817960446853120 else (if j.val < 272 then 30423614405477505635920893706240 else 60847228810955011271841787412480))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then 121694457621910022543683574824960 else 243388915243820045087367149649920) else (if j.val < 276 then 486777830487640090174734299299840 else (if j.val < 277 then 973555660975280180349468598599680 else 1947111321950560360698937197199360))) else (if j.val < 280 then (if j.val < 279 then 3894222643901120721397874394398720 else 7788445287802241442795748788797440) else (if j.val < 281 then 15576890575604482885591497577594880 else (if j.val < 282 then 31153781151208965771182995155189760 else 62307562302417931542365990310379520)))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then 124615124604835863084731980620759040 else 249230249209671726169463961241518080) else (if j.val < 286 then 498460498419343452338927922483036160 else (if j.val < 287 then 996920996838686904677855844966072320 else 1993841993677373809355711689932144640))) else (if j.val < 291 then (if j.val < 289 then 3987683987354747618711423379864289280 else (if j.val < 290 then 7975367974709495237422846759728578560 else 15950735949418990474845693519457157120)) else (if j.val < 292 then 31901471898837980949691387038914314240 else (if j.val < 293 then 63802943797675961899382774077828628480 else 127605887595351923798765548155657256960)))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then 255211775190703847597531096311314513920 else 510423550381407695195062192622629027840) else (if j.val < 297 then 1020847100762815390390124385245258055680 else (if j.val < 298 then 2041694201525630780780248770490516111360 else 4083388403051261561560497540981032222720))) else (if j.val < 301 then (if j.val < 300 then 8166776806102523123120995081962064445440 else 16333553612205046246241990163924128890880) else (if j.val < 302 then 32667107224410092492483980327848257781760 else (if j.val < 303 then 65334214448820184984967960655696515563520 else 130668428897640369969935921311393031127040)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then 261336857795280739939871842622786062254080 else 522673715590561479879743685245572124508160) else (if j.val < 307 then 1045347431181122959759487370491144249016320 else (if j.val < 308 then 2090694862362245919518974740982288498032640 else 4181389724724491839037949481964576996065280))) else (if j.val < 312 then (if j.val < 310 then 8362779449448983678075898963929153992130560 else (if j.val < 311 then 16725558898897967356151797927858307984261120 else 33451117797795934712303595855716615968522240)) else (if j.val < 313 then 66902235595591869424607191711433231937044480 else (if j.val < 314 then 133804471191183738849214383422866463874088960 else 267608942382367477698428766845732927748177920))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 535217884764734955396857533691465855496355840 else 1070435769529469910793715067382931710992711680) else (if j.val < 318 then 2140871539058939821587430134765863421985423360 else (if j.val < 319 then 4281743078117879643174860269531726843970846720 else 8563486156235759286349720539063453687941693440))) else (if j.val < 322 then (if j.val < 321 then 17126972312471518572699441078126907375883386880 else 34253944624943037145398882156253814751766773760) else (if j.val < 323 then 68507889249886074290797764312507629503533547520 else (if j.val < 324 then 137015778499772148581595528625015259007067095040 else 274031556999544297163191057250030518014134190080)))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then 548063113999088594326382114500061036028268380160 else 1096126227998177188652764229000122072056536760320) else (if j.val < 328 then 2192252455996354377305528458000244144113073520640 else (if j.val < 329 then 4384504911992708754611056916000488288226147041280 else 8769009823985417509222113832000976576452294082560))) else (if j.val < 333 then (if j.val < 331 then 17538019647970835018444227664001953152904588165120 else (if j.val < 332 then 35076039295941670036888435985190792471742381031425 else 70152078591883340073776871970381584943484762062850)) else (if j.val < 334 then 140304157183766680147553743940763169886969524125700 else (if j.val < 335 then 280608314367533360295107487881526339773939048251400 else 187072209578355573530071677930497340350026160799760)))))))))
def zH : Matrix (Fin 168) (Fin 336) (ZMod 2) := fun i j => entry (zmask j) i
end BB336C2KernelData

set_option maxHeartbeats 0
open Matrix BBCode
namespace BB336C2Symmetry

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
    have he := (BB336C2Cert.rowspace_reindex (HX A B) negG dualQ v)
    rw [HX_dual] at he
    exact hv.2 (he.mp h)
end BB336C2Symmetry

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336C2Cert BB336C2Bits
namespace BB336C2KernelData
def polyA : Poly 2 84 := {(0,0),(0,1),(1,5)}
def polyB : Poly 2 84 := {(0,0),(0,20),(0,46)}
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

namespace BB336C2Sparse

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
  | Sum.inr g => unit (er.symm (g-(0,0))) ^^^ unit (er.symm (g-(0,20))) ^^^ unit (er.symm (g-(0,46)))

lemma column_entry (i : Fin 168) (q : Qubit 2 84) :
    HX polyA polyB (er i) q = entry (column q) i := by
  cases q with
  | inl g => exact col_three (0,0) (0,1) (1,5) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three (0,0) (0,20) (0,46) g (by decide) (by decide) (by decide) i

lemma xcolumn_bits : ∀ j, xmask j = column (eqb j) := by decide +kernel
lemma xtable_sparse : (HX polyA polyB).submatrix er eqb = xH := by
  ext i j
  change HX polyA polyB (er i) (eqb j) = entry (xmask j) i
  rw [xcolumn_bits,column_entry]
end BB336C2Sparse

namespace BB336C2Sparse
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
  | Sum.inl g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,20))) ^^^ unit (er.symm (g+(0,46)))
  | Sum.inr g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,1))) ^^^ unit (er.symm (g+(1,5)))

lemma zcolumn_entry (i : Fin 168) (q : Qubit 2 84) :
    HZ polyA polyB (er i) q = entry (zcolumn q) i := by
  cases q with
  | inl g => exact col_three_z (0,0) (0,20) (0,46) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three_z (0,0) (0,1) (1,5) g (by decide) (by decide) (by decide) i

lemma zcolumn_bits : ∀ j, zmask j = zcolumn (eqb j) := by decide +kernel
lemma ztable_sparse : (HZ polyA polyB).submatrix er eqb = zH := by
  ext i j
  change HZ polyA polyB (er i) (eqb j) = entry (zmask j) i
  rw [zcolumn_bits,zcolumn_entry]
end BB336C2Sparse

lemma xtable : (HX polyA polyB).submatrix er eqb = xH := BB336C2Sparse.xtable_sparse
lemma ztable : (HZ polyA polyB).submatrix er eqb = zH := BB336C2Sparse.ztable_sparse
lemma xcolParity : ∀ j, ∑ i, xH i j = 1 := by
  intro j
  change ∑ i, entry (xmask j) i = 1
  rw [BB336C2Sparse.xcolumn_bits]
  cases hq : eqb j with
  | inl g => simp [BB336C2Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
  | inr g => simp [BB336C2Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
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
  unit (eqb.symm (Sum.inr (er i+(0,20)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,46))))
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
    exact indicator_three (0,0) (0,20) (0,46) (g-er i) (by decide) (by decide) (by decide)
lemma xrow_entry (i : Fin 168) (j : Fin 336) : entry (xrow i) j = xH i j := by
  rw [row_formula_bits,row_formula_entry]
  exact congrFun (congrFun xtable i) j
end BB336C2KernelData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336C2Cert BB336C2Bits
namespace BB336C2KernelData
def xrows (i : Fin 158) : Fin 168 := ⟨i.val, by omega⟩
def xpiv (i : Fin 158) : Fin 336 := ⟨i.val, by omega⟩
def xLmask (i : Fin 168) : BitVec 158 := BitVec.ofNat 158 (if i.val < 84 then (if i.val < 42 then (if i.val < 21 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 4 else (if i.val < 4 then 8 else 16))) else (if i.val < 7 then (if i.val < 6 then 32 else 64) else (if i.val < 8 then 128 else (if i.val < 9 then 256 else 512)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 1024 else 2048) else (if i.val < 13 then 4096 else (if i.val < 14 then 8192 else 16384))) else (if i.val < 18 then (if i.val < 16 then 32768 else (if i.val < 17 then 65536 else 131072)) else (if i.val < 19 then 262144 else (if i.val < 20 then 524288 else 1048576))))) else (if i.val < 31 then (if i.val < 26 then (if i.val < 23 then (if i.val < 22 then 2097152 else 4194304) else (if i.val < 24 then 8388608 else (if i.val < 25 then 16777216 else 33554432))) else (if i.val < 28 then (if i.val < 27 then 67108864 else 134217728) else (if i.val < 29 then 268435456 else (if i.val < 30 then 536870912 else 1073741824)))) else (if i.val < 36 then (if i.val < 33 then (if i.val < 32 then 2147483648 else 4294967296) else (if i.val < 34 then 8589934592 else (if i.val < 35 then 17179869184 else 34359738368))) else (if i.val < 39 then (if i.val < 37 then 68719476736 else (if i.val < 38 then 137438953472 else 274877906944)) else (if i.val < 40 then 549755813888 else (if i.val < 41 then 1099511627776 else 2199023255552)))))) else (if i.val < 63 then (if i.val < 52 then (if i.val < 47 then (if i.val < 44 then (if i.val < 43 then 4398046511104 else 8796093022208) else (if i.val < 45 then 17592186044416 else (if i.val < 46 then 35184372088832 else 70368744177664))) else (if i.val < 49 then (if i.val < 48 then 140737488355328 else 281474976710656) else (if i.val < 50 then 562949953421312 else (if i.val < 51 then 1125899906842624 else 2251799813685248)))) else (if i.val < 57 then (if i.val < 54 then (if i.val < 53 then 4503599627370496 else 9007199254740992) else (if i.val < 55 then 18014398509481984 else (if i.val < 56 then 36028797018963968 else 72057594037927936))) else (if i.val < 60 then (if i.val < 58 then 144115188075855872 else (if i.val < 59 then 288230376151711744 else 576460752303423488)) else (if i.val < 61 then 1152921504606846976 else (if i.val < 62 then 2305843009213693952 else 4611686018427387904))))) else (if i.val < 73 then (if i.val < 68 then (if i.val < 65 then (if i.val < 64 then 9223372036854775808 else 18446744073709551616) else (if i.val < 66 then 36893488147419103232 else (if i.val < 67 then 73786976294838206464 else 147573952589676412928))) else (if i.val < 70 then (if i.val < 69 then 295147905179352825856 else 590295810358705651712) else (if i.val < 71 then 1180591620717411303424 else (if i.val < 72 then 2361183241434822606848 else 4722366482869645213696)))) else (if i.val < 78 then (if i.val < 75 then (if i.val < 74 then 9444732965739290427392 else 18889465931478580854784) else (if i.val < 76 then 37778931862957161709568 else (if i.val < 77 then 75557863725914323419136 else 151115727451828646838272))) else (if i.val < 81 then (if i.val < 79 then 302231454903657293676544 else (if i.val < 80 then 604462909807314587353088 else 1208925819614629174706176)) else (if i.val < 82 then 2417851639229258349412352 else (if i.val < 83 then 4835703278458516698824704 else 9671406556917033397649408))))))) else (if i.val < 126 then (if i.val < 105 then (if i.val < 94 then (if i.val < 89 then (if i.val < 86 then (if i.val < 85 then 19342813113834066795298816 else 38685626227668133590597632) else (if i.val < 87 then 77371252455336267181195264 else (if i.val < 88 then 154742504910672534362390528 else 309485009821345068724781056))) else (if i.val < 91 then (if i.val < 90 then 618970019642690137449562112 else 1237940039285380274899124224) else (if i.val < 92 then 2475880078570760549798248448 else (if i.val < 93 then 4951760157141521099596496896 else 9903520314283042199192993792)))) else (if i.val < 99 then (if i.val < 96 then (if i.val < 95 then 19807040628566084398385987584 else 39614081257132168796771975168) else (if i.val < 97 then 79228162514264337593543950336 else (if i.val < 98 then 158456325028528675187087900672 else 316912650057057350374175801344))) else (if i.val < 102 then (if i.val < 100 then 633825300114114700748351602688 else (if i.val < 101 then 1267650600228229401496703205376 else 2535301200456458802993406410752)) else (if i.val < 103 then 5070602400912917605986812821504 else (if i.val < 104 then 10141204801825835211973625643008 else 20282409603651670423947251286016))))) else (if i.val < 115 then (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then 40564819207303340847894502572032 else 81129638414606681695789005144064) else (if i.val < 108 then 162259276829213363391578010288128 else (if i.val < 109 then 324518553658426726783156020576256 else 649037107316853453566312041152512))) else (if i.val < 112 then (if i.val < 111 then 1298074214633706907132624082305024 else 2596148429267413814265248164610048) else (if i.val < 113 then 5192296858534827628530496329220096 else (if i.val < 114 then 10384593717069655257060992658440192 else 20769187434139310514121985316880384)))) else (if i.val < 120 then (if i.val < 117 then (if i.val < 116 then 41538374868278621028243970633760768 else 83076749736557242056487941267521536) else (if i.val < 118 then 166153499473114484112975882535043072 else (if i.val < 119 then 332306998946228968225951765070086144 else 664613997892457936451903530140172288))) else (if i.val < 123 then (if i.val < 121 then 1329227995784915872903807060280344576 else (if i.val < 122 then 2658455991569831745807614120560689152 else 5316911983139663491615228241121378304)) else (if i.val < 124 then 10633823966279326983230456482242756608 else (if i.val < 125 then 21267647932558653966460912964485513216 else 42535295865117307932921825928971026432)))))) else (if i.val < 147 then (if i.val < 136 then (if i.val < 131 then (if i.val < 128 then (if i.val < 127 then 85070591730234615865843651857942052864 else 170141183460469231731687303715884105728) else (if i.val < 129 then 340282366920938463463374607431768211456 else (if i.val < 130 then 680564733841876926926749214863536422912 else 1361129467683753853853498429727072845824))) else (if i.val < 133 then (if i.val < 132 then 2722258935367507707706996859454145691648 else 5444517870735015415413993718908291383296) else (if i.val < 134 then 10889035741470030830827987437816582766592 else (if i.val < 135 then 21778071482940061661655974875633165533184 else 43556142965880123323311949751266331066368)))) else (if i.val < 141 then (if i.val < 138 then (if i.val < 137 then 87112285931760246646623899502532662132736 else 174224571863520493293247799005065324265472) else (if i.val < 139 then 348449143727040986586495598010130648530944 else (if i.val < 140 then 696898287454081973172991196020261297061888 else 1393796574908163946345982392040522594123776))) else (if i.val < 144 then (if i.val < 142 then 2787593149816327892691964784081045188247552 else (if i.val < 143 then 5575186299632655785383929568162090376495104 else 11150372599265311570767859136324180752990208)) else (if i.val < 145 then 22300745198530623141535718272648361505980416 else (if i.val < 146 then 44601490397061246283071436545296723011960832 else 89202980794122492566142873090593446023921664))))) else (if i.val < 157 then (if i.val < 152 then (if i.val < 149 then (if i.val < 148 then 178405961588244985132285746181186892047843328 else 356811923176489970264571492362373784095686656) else (if i.val < 150 then 713623846352979940529142984724747568191373312 else (if i.val < 151 then 1427247692705959881058285969449495136382746624 else 2854495385411919762116571938898990272765493248))) else (if i.val < 154 then (if i.val < 153 then 5708990770823839524233143877797980545530986496 else 11417981541647679048466287755595961091061972992) else (if i.val < 155 then 22835963083295358096932575511191922182123945984 else (if i.val < 156 then 45671926166590716193865151022383844364247891968 else 91343852333181432387730302044767688728495783936)))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then 182687704666362864775460604089535377456991567872 else 1790012260481073309520870559206667614435547551) else (if i.val < 160 then 3580024520962146619022398305299501162075796287 else (if i.val < 161 then 7160049041924293238025453797485168257356293759 else 14320098083848586476031564781856502447917288703))) else (if i.val < 165 then (if i.val < 163 then 28640196167697172952043786750599170829039278591 else (if i.val < 164 then 57280392335394345904068230688084507591283258367 else 114560784670788691808136461376169015182566516734)) else (if i.val < 166 then 229121569341577383616272922752338030365133033468 else (if i.val < 167 then 91791355398301700715120191091126272665502320231 else 183582710796603401430221039369138711264209341647))))))))
def xL : Matrix (Fin 168) (Fin 158) (ZMod 2) := fun i j => entry (xLmask i) j
def xR : Matrix (Fin 158) (Fin 336) (ZMod 2) := xH.submatrix xrows id
lemma xfactor_bits_0 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 0 := by decide +kernel
lemma xfactor_bits_1 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 1 := by decide +kernel
lemma xfactor_bits_2 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 2 := by decide +kernel
lemma xfactor_bits_3 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 3 := by decide +kernel
lemma xfactor_bits_4 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 4 := by decide +kernel
lemma xfactor_bits_5 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 5 := by decide +kernel
lemma xfactor_bits_6 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 6 := by decide +kernel
lemma xfactor_bits_7 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 7 := by decide +kernel
lemma xfactor_bits_8 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 8 := by decide +kernel
lemma xfactor_bits_9 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 9 := by decide +kernel
lemma xfactor_bits_10 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 10 := by decide +kernel
lemma xfactor_bits_11 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 11 := by decide +kernel
lemma xfactor_bits_12 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 12 := by decide +kernel
lemma xfactor_bits_13 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 13 := by decide +kernel
lemma xfactor_bits_14 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 14 := by decide +kernel
lemma xfactor_bits_15 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 15 := by decide +kernel
lemma xfactor_bits_16 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 16 := by decide +kernel
lemma xfactor_bits_17 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 17 := by decide +kernel
lemma xfactor_bits_18 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 18 := by decide +kernel
lemma xfactor_bits_19 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 19 := by decide +kernel
lemma xfactor_bits_20 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 20 := by decide +kernel
lemma xfactor_bits_21 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 21 := by decide +kernel
lemma xfactor_bits_22 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 22 := by decide +kernel
lemma xfactor_bits_23 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 23 := by decide +kernel
lemma xfactor_bits_24 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 24 := by decide +kernel
lemma xfactor_bits_25 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 25 := by decide +kernel
lemma xfactor_bits_26 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 26 := by decide +kernel
lemma xfactor_bits_27 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 27 := by decide +kernel
lemma xfactor_bits_28 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 28 := by decide +kernel
lemma xfactor_bits_29 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 29 := by decide +kernel
lemma xfactor_bits_30 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 30 := by decide +kernel
lemma xfactor_bits_31 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 31 := by decide +kernel
lemma xfactor_bits_32 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 32 := by decide +kernel
lemma xfactor_bits_33 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 33 := by decide +kernel
lemma xfactor_bits_34 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 34 := by decide +kernel
lemma xfactor_bits_35 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 35 := by decide +kernel
lemma xfactor_bits_36 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 36 := by decide +kernel
lemma xfactor_bits_37 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 37 := by decide +kernel
lemma xfactor_bits_38 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 38 := by decide +kernel
lemma xfactor_bits_39 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 39 := by decide +kernel
lemma xfactor_bits_40 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 40 := by decide +kernel
lemma xfactor_bits_41 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 41 := by decide +kernel
lemma xfactor_bits_42 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 42 := by decide +kernel
lemma xfactor_bits_43 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 43 := by decide +kernel
lemma xfactor_bits_44 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 44 := by decide +kernel
lemma xfactor_bits_45 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 45 := by decide +kernel
lemma xfactor_bits_46 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 46 := by decide +kernel
lemma xfactor_bits_47 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 47 := by decide +kernel
lemma xfactor_bits_48 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 48 := by decide +kernel
lemma xfactor_bits_49 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 49 := by decide +kernel
lemma xfactor_bits_50 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 50 := by decide +kernel
lemma xfactor_bits_51 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 51 := by decide +kernel
lemma xfactor_bits_52 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 52 := by decide +kernel
lemma xfactor_bits_53 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 53 := by decide +kernel
lemma xfactor_bits_54 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 54 := by decide +kernel
lemma xfactor_bits_55 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 55 := by decide +kernel
lemma xfactor_bits_56 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 56 := by decide +kernel
lemma xfactor_bits_57 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 57 := by decide +kernel
lemma xfactor_bits_58 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 58 := by decide +kernel
lemma xfactor_bits_59 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 59 := by decide +kernel
lemma xfactor_bits_60 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 60 := by decide +kernel
lemma xfactor_bits_61 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 61 := by decide +kernel
lemma xfactor_bits_62 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 62 := by decide +kernel
lemma xfactor_bits_63 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 63 := by decide +kernel
lemma xfactor_bits_64 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 64 := by decide +kernel
lemma xfactor_bits_65 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 65 := by decide +kernel
lemma xfactor_bits_66 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 66 := by decide +kernel
lemma xfactor_bits_67 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 67 := by decide +kernel
lemma xfactor_bits_68 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 68 := by decide +kernel
lemma xfactor_bits_69 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 69 := by decide +kernel
lemma xfactor_bits_70 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 70 := by decide +kernel
lemma xfactor_bits_71 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 71 := by decide +kernel
lemma xfactor_bits_72 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 72 := by decide +kernel
lemma xfactor_bits_73 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 73 := by decide +kernel
lemma xfactor_bits_74 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 74 := by decide +kernel
lemma xfactor_bits_75 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 75 := by decide +kernel
lemma xfactor_bits_76 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 76 := by decide +kernel
lemma xfactor_bits_77 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 77 := by decide +kernel
lemma xfactor_bits_78 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 78 := by decide +kernel
lemma xfactor_bits_79 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 79 := by decide +kernel
lemma xfactor_bits_80 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 80 := by decide +kernel
lemma xfactor_bits_81 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 81 := by decide +kernel
lemma xfactor_bits_82 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 82 := by decide +kernel
lemma xfactor_bits_83 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 83 := by decide +kernel
lemma xfactor_bits_84 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 84 := by decide +kernel
lemma xfactor_bits_85 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 85 := by decide +kernel
lemma xfactor_bits_86 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 86 := by decide +kernel
lemma xfactor_bits_87 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 87 := by decide +kernel
lemma xfactor_bits_88 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 88 := by decide +kernel
lemma xfactor_bits_89 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 89 := by decide +kernel
lemma xfactor_bits_90 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 90 := by decide +kernel
lemma xfactor_bits_91 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 91 := by decide +kernel
lemma xfactor_bits_92 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 92 := by decide +kernel
lemma xfactor_bits_93 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 93 := by decide +kernel
lemma xfactor_bits_94 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 94 := by decide +kernel
lemma xfactor_bits_95 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 95 := by decide +kernel
lemma xfactor_bits_96 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 96 := by decide +kernel
lemma xfactor_bits_97 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 97 := by decide +kernel
lemma xfactor_bits_98 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 98 := by decide +kernel
lemma xfactor_bits_99 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 99 := by decide +kernel
lemma xfactor_bits_100 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 100 := by decide +kernel
lemma xfactor_bits_101 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 101 := by decide +kernel
lemma xfactor_bits_102 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 102 := by decide +kernel
lemma xfactor_bits_103 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 103 := by decide +kernel
lemma xfactor_bits_104 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 104 := by decide +kernel
lemma xfactor_bits_105 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 105 := by decide +kernel
lemma xfactor_bits_106 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 106 := by decide +kernel
lemma xfactor_bits_107 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 107 := by decide +kernel
lemma xfactor_bits_108 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 108 := by decide +kernel
lemma xfactor_bits_109 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 109 := by decide +kernel
lemma xfactor_bits_110 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 110 := by decide +kernel
lemma xfactor_bits_111 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 111 := by decide +kernel
lemma xfactor_bits_112 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 112 := by decide +kernel
lemma xfactor_bits_113 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 113 := by decide +kernel
lemma xfactor_bits_114 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 114 := by decide +kernel
lemma xfactor_bits_115 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 115 := by decide +kernel
lemma xfactor_bits_116 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 116 := by decide +kernel
lemma xfactor_bits_117 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 117 := by decide +kernel
lemma xfactor_bits_118 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 118 := by decide +kernel
lemma xfactor_bits_119 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 119 := by decide +kernel
lemma xfactor_bits_120 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 120 := by decide +kernel
lemma xfactor_bits_121 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 121 := by decide +kernel
lemma xfactor_bits_122 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 122 := by decide +kernel
lemma xfactor_bits_123 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 123 := by decide +kernel
lemma xfactor_bits_124 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 124 := by decide +kernel
lemma xfactor_bits_125 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 125 := by decide +kernel
lemma xfactor_bits_126 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 126 := by decide +kernel
lemma xfactor_bits_127 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 127 := by decide +kernel
lemma xfactor_bits_128 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 128 := by decide +kernel
lemma xfactor_bits_129 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 129 := by decide +kernel
lemma xfactor_bits_130 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 130 := by decide +kernel
lemma xfactor_bits_131 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 131 := by decide +kernel
lemma xfactor_bits_132 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 132 := by decide +kernel
lemma xfactor_bits_133 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 133 := by decide +kernel
lemma xfactor_bits_134 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 134 := by decide +kernel
lemma xfactor_bits_135 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 135 := by decide +kernel
lemma xfactor_bits_136 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 136 := by decide +kernel
lemma xfactor_bits_137 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 137 := by decide +kernel
lemma xfactor_bits_138 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 138 := by decide +kernel
lemma xfactor_bits_139 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 139 := by decide +kernel
lemma xfactor_bits_140 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 140 := by decide +kernel
lemma xfactor_bits_141 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 141 := by decide +kernel
lemma xfactor_bits_142 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 142 := by decide +kernel
lemma xfactor_bits_143 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 143 := by decide +kernel
lemma xfactor_bits_144 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 144 := by decide +kernel
lemma xfactor_bits_145 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 145 := by decide +kernel
lemma xfactor_bits_146 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 146 := by decide +kernel
lemma xfactor_bits_147 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 147 := by decide +kernel
lemma xfactor_bits_148 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 148 := by decide +kernel
lemma xfactor_bits_149 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 149 := by decide +kernel
lemma xfactor_bits_150 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 150 := by decide +kernel
lemma xfactor_bits_151 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 151 := by decide +kernel
lemma xfactor_bits_152 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 152 := by decide +kernel
lemma xfactor_bits_153 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 153 := by decide +kernel
lemma xfactor_bits_154 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 154 := by decide +kernel
lemma xfactor_bits_155 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 155 := by decide +kernel
lemma xfactor_bits_156 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 156 := by decide +kernel
lemma xfactor_bits_157 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 157 := by decide +kernel
lemma xfactor_bits_158 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 158 := by decide +kernel
lemma xfactor_bits_159 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 159 := by decide +kernel
lemma xfactor_bits_160 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 160 := by decide +kernel
lemma xfactor_bits_161 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 161 := by decide +kernel
lemma xfactor_bits_162 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 162 := by decide +kernel
lemma xfactor_bits_163 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 163 := by decide +kernel
lemma xfactor_bits_164 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 164 := by decide +kernel
lemma xfactor_bits_165 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 165 := by decide +kernel
lemma xfactor_bits_166 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 166 := by decide +kernel
lemma xfactor_bits_167 : (fun i : Fin 168 => combination (fun j => xrow (xrows j)) (xLmask i) = xrow i) 167 := by decide +kernel
lemma xfactor_bits : ∀ i, combination (fun j => xrow (xrows j)) (xLmask i) = xrow i := by
  intro i
  fin_cases i
  · exact xfactor_bits_0
  · exact xfactor_bits_1
  · exact xfactor_bits_2
  · exact xfactor_bits_3
  · exact xfactor_bits_4
  · exact xfactor_bits_5
  · exact xfactor_bits_6
  · exact xfactor_bits_7
  · exact xfactor_bits_8
  · exact xfactor_bits_9
  · exact xfactor_bits_10
  · exact xfactor_bits_11
  · exact xfactor_bits_12
  · exact xfactor_bits_13
  · exact xfactor_bits_14
  · exact xfactor_bits_15
  · exact xfactor_bits_16
  · exact xfactor_bits_17
  · exact xfactor_bits_18
  · exact xfactor_bits_19
  · exact xfactor_bits_20
  · exact xfactor_bits_21
  · exact xfactor_bits_22
  · exact xfactor_bits_23
  · exact xfactor_bits_24
  · exact xfactor_bits_25
  · exact xfactor_bits_26
  · exact xfactor_bits_27
  · exact xfactor_bits_28
  · exact xfactor_bits_29
  · exact xfactor_bits_30
  · exact xfactor_bits_31
  · exact xfactor_bits_32
  · exact xfactor_bits_33
  · exact xfactor_bits_34
  · exact xfactor_bits_35
  · exact xfactor_bits_36
  · exact xfactor_bits_37
  · exact xfactor_bits_38
  · exact xfactor_bits_39
  · exact xfactor_bits_40
  · exact xfactor_bits_41
  · exact xfactor_bits_42
  · exact xfactor_bits_43
  · exact xfactor_bits_44
  · exact xfactor_bits_45
  · exact xfactor_bits_46
  · exact xfactor_bits_47
  · exact xfactor_bits_48
  · exact xfactor_bits_49
  · exact xfactor_bits_50
  · exact xfactor_bits_51
  · exact xfactor_bits_52
  · exact xfactor_bits_53
  · exact xfactor_bits_54
  · exact xfactor_bits_55
  · exact xfactor_bits_56
  · exact xfactor_bits_57
  · exact xfactor_bits_58
  · exact xfactor_bits_59
  · exact xfactor_bits_60
  · exact xfactor_bits_61
  · exact xfactor_bits_62
  · exact xfactor_bits_63
  · exact xfactor_bits_64
  · exact xfactor_bits_65
  · exact xfactor_bits_66
  · exact xfactor_bits_67
  · exact xfactor_bits_68
  · exact xfactor_bits_69
  · exact xfactor_bits_70
  · exact xfactor_bits_71
  · exact xfactor_bits_72
  · exact xfactor_bits_73
  · exact xfactor_bits_74
  · exact xfactor_bits_75
  · exact xfactor_bits_76
  · exact xfactor_bits_77
  · exact xfactor_bits_78
  · exact xfactor_bits_79
  · exact xfactor_bits_80
  · exact xfactor_bits_81
  · exact xfactor_bits_82
  · exact xfactor_bits_83
  · exact xfactor_bits_84
  · exact xfactor_bits_85
  · exact xfactor_bits_86
  · exact xfactor_bits_87
  · exact xfactor_bits_88
  · exact xfactor_bits_89
  · exact xfactor_bits_90
  · exact xfactor_bits_91
  · exact xfactor_bits_92
  · exact xfactor_bits_93
  · exact xfactor_bits_94
  · exact xfactor_bits_95
  · exact xfactor_bits_96
  · exact xfactor_bits_97
  · exact xfactor_bits_98
  · exact xfactor_bits_99
  · exact xfactor_bits_100
  · exact xfactor_bits_101
  · exact xfactor_bits_102
  · exact xfactor_bits_103
  · exact xfactor_bits_104
  · exact xfactor_bits_105
  · exact xfactor_bits_106
  · exact xfactor_bits_107
  · exact xfactor_bits_108
  · exact xfactor_bits_109
  · exact xfactor_bits_110
  · exact xfactor_bits_111
  · exact xfactor_bits_112
  · exact xfactor_bits_113
  · exact xfactor_bits_114
  · exact xfactor_bits_115
  · exact xfactor_bits_116
  · exact xfactor_bits_117
  · exact xfactor_bits_118
  · exact xfactor_bits_119
  · exact xfactor_bits_120
  · exact xfactor_bits_121
  · exact xfactor_bits_122
  · exact xfactor_bits_123
  · exact xfactor_bits_124
  · exact xfactor_bits_125
  · exact xfactor_bits_126
  · exact xfactor_bits_127
  · exact xfactor_bits_128
  · exact xfactor_bits_129
  · exact xfactor_bits_130
  · exact xfactor_bits_131
  · exact xfactor_bits_132
  · exact xfactor_bits_133
  · exact xfactor_bits_134
  · exact xfactor_bits_135
  · exact xfactor_bits_136
  · exact xfactor_bits_137
  · exact xfactor_bits_138
  · exact xfactor_bits_139
  · exact xfactor_bits_140
  · exact xfactor_bits_141
  · exact xfactor_bits_142
  · exact xfactor_bits_143
  · exact xfactor_bits_144
  · exact xfactor_bits_145
  · exact xfactor_bits_146
  · exact xfactor_bits_147
  · exact xfactor_bits_148
  · exact xfactor_bits_149
  · exact xfactor_bits_150
  · exact xfactor_bits_151
  · exact xfactor_bits_152
  · exact xfactor_bits_153
  · exact xfactor_bits_154
  · exact xfactor_bits_155
  · exact xfactor_bits_156
  · exact xfactor_bits_157
  · exact xfactor_bits_158
  · exact xfactor_bits_159
  · exact xfactor_bits_160
  · exact xfactor_bits_161
  · exact xfactor_bits_162
  · exact xfactor_bits_163
  · exact xfactor_bits_164
  · exact xfactor_bits_165
  · exact xfactor_bits_166
  · exact xfactor_bits_167
lemma xfactor : xH = xL * xR := by
  have h := product xLmask (fun j => xrow (xrows j)) xrow xfactor_bits
  have he : (Matrix.of fun i j => entry (xrow i) j) = xH := by
    apply Matrix.ext; intro i j; exact xrow_entry i j
  have hr : (Matrix.of fun i j => entry (xrow (xrows i)) j) = xR := by
    apply Matrix.ext; intro i j; exact xrow_entry (xrows i) j
  rw [he,hr] at h
  exact h.symm
def xMmask (i : Fin 158) : BitVec 158 := (xrow (xrows i)).setWidth 158
def xImask (i : Fin 158) : BitVec 158 := BitVec.ofNat 158 (if i.val < 79 then (if i.val < 39 then (if i.val < 19 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57280392335394345904068230688084507591283258367 else 114560784670788691808136461376169015182566516734) else (if i.val < 3 then 229121569341577383616272922752338030365133033468 else 91791355398301700715120191091126272665502320231)) else (if i.val < 6 then (if i.val < 5 then 187525470961339148672769537195298754330295608943 else 6095508068990421175575527734621046407386529760) else (if i.val < 7 then 12191016137980842351151055469242092814773059520 else (if i.val < 8 then 24382032275961684702302110938484185629546119040 else 48764064551923369404604221876968371259092238080)))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then 97528129103846738809208443753936742518184476160 else 195056258207693477618416887507873485036368952320) else (if i.val < 12 then 22947838849575425180027659218623865474672353695 else (if i.val < 13 then 51264226425803524681345397391136091987878472095 else 97170277633076115713546908465810321092496193951))) else (if i.val < 16 then (if i.val < 15 then 199686868921770878796817172814362151733942147487 else 30418303989853881423670794264101577907282870272) else (if i.val < 17 then 60836607979707762847341588528203155814565740544 else (if i.val < 18 then 121673215959415525694683177056406311629131481088 else 243346431918831051389366354112812623258262962176))))) else (if i.val < 29 then (if i.val < 24 then (if i.val < 21 then (if i.val < 20 then 120252957768544047401096825238701343299885996447 else 244424921270353819765143262638389462700254960031) else (if i.val < 22 then 119894408687019763360322978618417789552425959424 else (if i.val < 23 then 239788817374039526720645957236835579104851918848 else 115992193438960543978418208589220052339947084191))) else (if i.val < 26 then (if i.val < 25 then 230194463091187721090261675143721531228907510175 else 91433492328687566010559803610601436325137612800) else (if i.val < 27 then 182866984657375132021119607221202872650275225600 else (if i.val < 28 then 1434239928098544966955685062534201167186893215 else 2507132224530142292156276254845691986595158431)))) else (if i.val < 34 then (if i.val < 31 then (if i.val < 30 then 358559982024941493003479661258651951247006111 else 4658492116677349240060689416240355222566607263) else (if i.val < 32 then 7515809860532701086652146483305023408690829727 else (if i.val < 33 then 13263931685266177031678332635685064461124508063 else 24737107082656008121884827580745435851284945311))) else (if i.val < 36 then (if i.val < 35 then 47685689959621488198148905475384559191055014303 else 92867729350408329006362495749358943329866095007) else (if i.val < 37 then 185372723057042732864031195651128855772077627807 else (if i.val < 38 then 1790012260397589558098839919226518108085682176 else 3580024520795179116197679838453036216171364352)))))) else (if i.val < 59 then (if i.val < 49 then (if i.val < 44 then (if i.val < 41 then (if i.val < 40 then 7160049041590358232395359676906072432342728704 else 14320098083180716464790719353812144864685457408) else (if i.val < 42 then 28640196166361432929581438707624289729370914816 else (if i.val < 43 then 57280392332722865859162877415248579458741829632 else 114560784665445731718325754830497158917483659264))) else (if i.val < 46 then (if i.val < 45 then 229121569330891463436651509660994317834967318528 else 91791355377096665596118842045275910180242856351) else (if i.val < 47 then 187525470918595467954283884829923904485318334879 else (if i.val < 48 then 6095507983503059738604223003871346166060810240 else 12191015967006119477208446007742692332121620480)))) else (if i.val < 54 then (if i.val < 51 then (if i.val < 50 then 24382031934012238954416892015485384664243240960 else 48764063868024477908833784030970769328486481920) else (if i.val < 52 then 97528127736048955817667568061941538656972963840 else (if i.val < 53 then 195056255472097911635335136123883077313945927680 else 22947844267587002015053448286019277389769349535))) else (if i.val < 56 then (if i.val < 55 then 51264215483421260749018391855174566926721358239 else 97170299474596548485869598504341284116248795551) else (if i.val < 57 then 199686825152241823067509150670515770837079824799 else (if i.val < 58 then 30418216450795769965054749976408530789746081792 else 60836432901591539930109499952817061579492163584))))) else (if i.val < 69 then (if i.val < 64 then (if i.val < 61 then (if i.val < 60 then 121672865803183079860218999905634123158984327168 else 243345731606366159720437999811268246317968654336) else (if i.val < 62 then 120251570755075743437359086508163494856108153247 else (if i.val < 63 then 244422120020494253089429845432230101554667854239 else 119888806187300630008896144206062774030071496704))) else (if i.val < 66 then (if i.val < 65 then 239777612374601260017792288412125548060142993408 else 115969827676957863794184235662612146668504488351) else (if i.val < 67 then 230149643093434654278846999844882680560219986335 else (if i.val < 68 then 91343852333181432387730453012921187967466209280 else 182687704666362864775460906025842375934932418560)))) else (if i.val < 74 then (if i.val < 71 then (if i.val < 70 then 1790012260481073309521470890045802418083338655 else 1790012260481073309521471480341612776788990367) else (if i.val < 72 then 1790012260481073309521472660933233494200293791 else (if i.val < 73 then 1790012260481073309521470299749992059377686943 else 1790012260481073309521465577383509189732473247))) else (if i.val < 76 then (if i.val < 75 then 1790012260481073309521456132650543450442045855 else 1790012260481073309521437243184611971861191071) else (if i.val < 77 then 1790012260481073309521399464252749014699481503 else (if i.val < 78 then 1790012260481073309521323906389023100376062367 else 1790012260481073309521172790661571271729224095))))))) else (if i.val < 118 then (if i.val < 98 then (if i.val < 88 then (if i.val < 83 then (if i.val < 81 then (if i.val < 80 then 1790012260481073309520870559206667614435547551 else 3580024520962146619022398305299501162075796287) else (if i.val < 82 then 7160049041924293238025453797485168257356293759 else 14320098083848586476031564781856502447917288703)) else (if i.val < 85 then (if i.val < 84 then 28640196167697172952043786750599170829039278591 else 5370036781443219928506394249645218564770245280) else (if i.val < 86 then 10740073562886439857012788499290437129540490560 else (if i.val < 87 then 21480147125772879714025576998580874259080981120 else 42960294251545759428051153997161748518161962240)))) else (if i.val < 93 then (if i.val < 90 then (if i.val < 89 then 85920588503091518856102307994323497036323924480 else 171841177006183037712204615988646994072647848960) else (if i.val < 91 then 343682354012366075424409231977293988145295697920 else (if i.val < 92 then 320912924739879084331392810723957219972812065183 else 278603188051287113044872698909053880524646031360))) else (if i.val < 95 then (if i.val < 94 then 192895507742782368601295275437506076049264040351 else 18286524206971263526726566636093450042047365120) else (if i.val < 96 then 36573048413942527053453133272186900084094730240 else (if i.val < 97 then 73146096827885054106906266544373800168189460480 else 146292193655770108213812533088747600336378920960))))) else (if i.val < 108 then (if i.val < 103 then (if i.val < 100 then (if i.val < 99 then 292584387311540216427625066177495200672757841920 else 218004097057268902798444017746583419989001116063) else (if i.val < 101 then 74211321247983677057736035709858730634494607360 else (if i.val < 102 then 148422642495967354115472071419717461268989214720 else 296845284991934708230944142839434922537978429440))) else (if i.val < 105 then (if i.val < 104 then 226537052828986978419638811564832183211574303135 else 91254911969561644271012342357617618095376957440) else (if i.val < 106 then 182509823939123288542024684715235236190753914880 else (if i.val < 107 then 365019647878246577084049369430470472381507829760 else 363599389687375098790462857066135654097615722911)))) else (if i.val < 113 then (if i.val < 110 then (if i.val < 109 then 363952363514809119683433248721759817469494558720 else 364308124969288273503798891599522203860144626079) else (if i.val < 111 then 359683226061059290080968765886917197821441474560 else (if i.val < 112 then 355781010813000070699063829431122299600762706335 else 342606676246059971671110834547546719229229137920))) else (if i.val < 115 then (if i.val < 114 then 321627255629021560691398104561233787762874653087 else 274300476986062698031679109190064804860379791360) else (if i.val < 116 then 184301224585473676988074692543189236290611452319 else (if i.val < 117 then 1075679946073603473952207760137147384982405120 else 2151359892147206947904415520274294769964810240)))))) else (if i.val < 138 then (if i.val < 128 then (if i.val < 123 then (if i.val < 120 then (if i.val < 119 then 4302719784294413895808831040548589539929620480 else 8605439568588827791617662081097179079859240960) else (if i.val < 121 then 17210879137177655583235324162194358159718481920 else (if i.val < 122 then 34421758274355311166470648324388716319436963840 else 68843516548710622332941296648777432638873927680))) else (if i.val < 125 then (if i.val < 124 then 137687033097421244665882593297554865277747855360 else 275374066194842489331765186595109730555495710720) else (if i.val < 126 then 183582710796645143305932356920583689605958474143 else (if i.val < 127 then 5370036781192768674296517380316850165446082560 else 10740073562385537348593034760633700330892165120)))) else (if i.val < 133 then (if i.val < 130 then (if i.val < 129 then 21480147124771074697186069521267400661784330240 else 42960294249542149394372139042534801323568660480) else (if i.val < 131 then 85920588499084298788744278085069602647137320960 else (if i.val < 132 then 171841176998168597577488556170139205294274641920 else 343682353996337195154977112340278410588549283840))) else (if i.val < 135 then (if i.val < 134 then 320912924707988129032770048586763162618494327199 else 278603187987171591967144220360991570297660375040) else (if i.val < 136 then 192895507784858828358815019255532746239463266719 else (if i.val < 137 then 18286523950509179215812652443844209134104739840 else 36573047901018358431625304887688418268209479680))))) else (if i.val < 148 then (if i.val < 143 then (if i.val < 140 then (if i.val < 139 then 73146095802036716863250609775376836536418959360 else 146292191604073433726501219550753673072837918720) else (if i.val < 141 then 292584383208146867453002439101507346145675837440 else (if i.val < 142 then 218004099739684913650388055429983929498416847263 else 74211304834410281159245527405907312526166589440))) else (if i.val < 145 then (if i.val < 144 then 148422609668820562318491054811814625052333178880 else 296845219337641124636982109623629250104666357760) else (if i.val < 146 then 226536922371272693329918164342587433634005653919 else (if i.val < 147 then 91254649352387309895164209494394928362128670720 else 182509298704774619790328418988789856724257341440)))) else (if i.val < 153 then (if i.val < 150 then (if i.val < 149 then 365018597409549239580656837977579713448514682880 else 363597302361441903157796764035213107889893677471) else (if i.val < 151 then 363948161640019769669863122910196781737521971200 else (if i.val < 152 then 364310926207794883098325908200529476175496354207 else 359666418561901890026688262640665054893551124480))) else (if i.val < 155 then (if i.val < 154 then 355747440051559123811976187661466022487554660767 else 342539446249430371453988821562538147517667737600) else (if i.val < 156 then 321493495426616086666577305505212207735787887007 else (if i.val < 157 then 274031556999544297163191057250030518014134190080 else 184477716926843938084981776880196948728720791967))))))))
def xInv : Matrix (Fin 158) (Fin 158) (ZMod 2) := fun i j => entry (xImask i) j
lemma xminor_bits_0 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 0 := by decide +kernel
lemma xminor_bits_1 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 1 := by decide +kernel
lemma xminor_bits_2 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 2 := by decide +kernel
lemma xminor_bits_3 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 3 := by decide +kernel
lemma xminor_bits_4 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 4 := by decide +kernel
lemma xminor_bits_5 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 5 := by decide +kernel
lemma xminor_bits_6 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 6 := by decide +kernel
lemma xminor_bits_7 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 7 := by decide +kernel
lemma xminor_bits_8 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 8 := by decide +kernel
lemma xminor_bits_9 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 9 := by decide +kernel
lemma xminor_bits_10 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 10 := by decide +kernel
lemma xminor_bits_11 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 11 := by decide +kernel
lemma xminor_bits_12 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 12 := by decide +kernel
lemma xminor_bits_13 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 13 := by decide +kernel
lemma xminor_bits_14 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 14 := by decide +kernel
lemma xminor_bits_15 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 15 := by decide +kernel
lemma xminor_bits_16 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 16 := by decide +kernel
lemma xminor_bits_17 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 17 := by decide +kernel
lemma xminor_bits_18 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 18 := by decide +kernel
lemma xminor_bits_19 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 19 := by decide +kernel
lemma xminor_bits_20 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 20 := by decide +kernel
lemma xminor_bits_21 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 21 := by decide +kernel
lemma xminor_bits_22 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 22 := by decide +kernel
lemma xminor_bits_23 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 23 := by decide +kernel
lemma xminor_bits_24 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 24 := by decide +kernel
lemma xminor_bits_25 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 25 := by decide +kernel
lemma xminor_bits_26 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 26 := by decide +kernel
lemma xminor_bits_27 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 27 := by decide +kernel
lemma xminor_bits_28 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 28 := by decide +kernel
lemma xminor_bits_29 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 29 := by decide +kernel
lemma xminor_bits_30 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 30 := by decide +kernel
lemma xminor_bits_31 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 31 := by decide +kernel
lemma xminor_bits_32 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 32 := by decide +kernel
lemma xminor_bits_33 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 33 := by decide +kernel
lemma xminor_bits_34 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 34 := by decide +kernel
lemma xminor_bits_35 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 35 := by decide +kernel
lemma xminor_bits_36 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 36 := by decide +kernel
lemma xminor_bits_37 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 37 := by decide +kernel
lemma xminor_bits_38 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 38 := by decide +kernel
lemma xminor_bits_39 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 39 := by decide +kernel
lemma xminor_bits_40 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 40 := by decide +kernel
lemma xminor_bits_41 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 41 := by decide +kernel
lemma xminor_bits_42 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 42 := by decide +kernel
lemma xminor_bits_43 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 43 := by decide +kernel
lemma xminor_bits_44 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 44 := by decide +kernel
lemma xminor_bits_45 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 45 := by decide +kernel
lemma xminor_bits_46 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 46 := by decide +kernel
lemma xminor_bits_47 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 47 := by decide +kernel
lemma xminor_bits_48 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 48 := by decide +kernel
lemma xminor_bits_49 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 49 := by decide +kernel
lemma xminor_bits_50 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 50 := by decide +kernel
lemma xminor_bits_51 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 51 := by decide +kernel
lemma xminor_bits_52 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 52 := by decide +kernel
lemma xminor_bits_53 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 53 := by decide +kernel
lemma xminor_bits_54 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 54 := by decide +kernel
lemma xminor_bits_55 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 55 := by decide +kernel
lemma xminor_bits_56 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 56 := by decide +kernel
lemma xminor_bits_57 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 57 := by decide +kernel
lemma xminor_bits_58 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 58 := by decide +kernel
lemma xminor_bits_59 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 59 := by decide +kernel
lemma xminor_bits_60 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 60 := by decide +kernel
lemma xminor_bits_61 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 61 := by decide +kernel
lemma xminor_bits_62 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 62 := by decide +kernel
lemma xminor_bits_63 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 63 := by decide +kernel
lemma xminor_bits_64 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 64 := by decide +kernel
lemma xminor_bits_65 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 65 := by decide +kernel
lemma xminor_bits_66 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 66 := by decide +kernel
lemma xminor_bits_67 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 67 := by decide +kernel
lemma xminor_bits_68 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 68 := by decide +kernel
lemma xminor_bits_69 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 69 := by decide +kernel
lemma xminor_bits_70 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 70 := by decide +kernel
lemma xminor_bits_71 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 71 := by decide +kernel
lemma xminor_bits_72 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 72 := by decide +kernel
lemma xminor_bits_73 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 73 := by decide +kernel
lemma xminor_bits_74 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 74 := by decide +kernel
lemma xminor_bits_75 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 75 := by decide +kernel
lemma xminor_bits_76 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 76 := by decide +kernel
lemma xminor_bits_77 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 77 := by decide +kernel
lemma xminor_bits_78 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 78 := by decide +kernel
lemma xminor_bits_79 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 79 := by decide +kernel
lemma xminor_bits_80 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 80 := by decide +kernel
lemma xminor_bits_81 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 81 := by decide +kernel
lemma xminor_bits_82 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 82 := by decide +kernel
lemma xminor_bits_83 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 83 := by decide +kernel
lemma xminor_bits_84 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 84 := by decide +kernel
lemma xminor_bits_85 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 85 := by decide +kernel
lemma xminor_bits_86 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 86 := by decide +kernel
lemma xminor_bits_87 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 87 := by decide +kernel
lemma xminor_bits_88 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 88 := by decide +kernel
lemma xminor_bits_89 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 89 := by decide +kernel
lemma xminor_bits_90 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 90 := by decide +kernel
lemma xminor_bits_91 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 91 := by decide +kernel
lemma xminor_bits_92 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 92 := by decide +kernel
lemma xminor_bits_93 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 93 := by decide +kernel
lemma xminor_bits_94 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 94 := by decide +kernel
lemma xminor_bits_95 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 95 := by decide +kernel
lemma xminor_bits_96 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 96 := by decide +kernel
lemma xminor_bits_97 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 97 := by decide +kernel
lemma xminor_bits_98 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 98 := by decide +kernel
lemma xminor_bits_99 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 99 := by decide +kernel
lemma xminor_bits_100 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 100 := by decide +kernel
lemma xminor_bits_101 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 101 := by decide +kernel
lemma xminor_bits_102 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 102 := by decide +kernel
lemma xminor_bits_103 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 103 := by decide +kernel
lemma xminor_bits_104 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 104 := by decide +kernel
lemma xminor_bits_105 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 105 := by decide +kernel
lemma xminor_bits_106 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 106 := by decide +kernel
lemma xminor_bits_107 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 107 := by decide +kernel
lemma xminor_bits_108 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 108 := by decide +kernel
lemma xminor_bits_109 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 109 := by decide +kernel
lemma xminor_bits_110 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 110 := by decide +kernel
lemma xminor_bits_111 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 111 := by decide +kernel
lemma xminor_bits_112 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 112 := by decide +kernel
lemma xminor_bits_113 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 113 := by decide +kernel
lemma xminor_bits_114 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 114 := by decide +kernel
lemma xminor_bits_115 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 115 := by decide +kernel
lemma xminor_bits_116 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 116 := by decide +kernel
lemma xminor_bits_117 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 117 := by decide +kernel
lemma xminor_bits_118 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 118 := by decide +kernel
lemma xminor_bits_119 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 119 := by decide +kernel
lemma xminor_bits_120 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 120 := by decide +kernel
lemma xminor_bits_121 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 121 := by decide +kernel
lemma xminor_bits_122 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 122 := by decide +kernel
lemma xminor_bits_123 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 123 := by decide +kernel
lemma xminor_bits_124 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 124 := by decide +kernel
lemma xminor_bits_125 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 125 := by decide +kernel
lemma xminor_bits_126 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 126 := by decide +kernel
lemma xminor_bits_127 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 127 := by decide +kernel
lemma xminor_bits_128 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 128 := by decide +kernel
lemma xminor_bits_129 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 129 := by decide +kernel
lemma xminor_bits_130 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 130 := by decide +kernel
lemma xminor_bits_131 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 131 := by decide +kernel
lemma xminor_bits_132 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 132 := by decide +kernel
lemma xminor_bits_133 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 133 := by decide +kernel
lemma xminor_bits_134 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 134 := by decide +kernel
lemma xminor_bits_135 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 135 := by decide +kernel
lemma xminor_bits_136 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 136 := by decide +kernel
lemma xminor_bits_137 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 137 := by decide +kernel
lemma xminor_bits_138 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 138 := by decide +kernel
lemma xminor_bits_139 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 139 := by decide +kernel
lemma xminor_bits_140 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 140 := by decide +kernel
lemma xminor_bits_141 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 141 := by decide +kernel
lemma xminor_bits_142 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 142 := by decide +kernel
lemma xminor_bits_143 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 143 := by decide +kernel
lemma xminor_bits_144 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 144 := by decide +kernel
lemma xminor_bits_145 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 145 := by decide +kernel
lemma xminor_bits_146 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 146 := by decide +kernel
lemma xminor_bits_147 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 147 := by decide +kernel
lemma xminor_bits_148 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 148 := by decide +kernel
lemma xminor_bits_149 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 149 := by decide +kernel
lemma xminor_bits_150 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 150 := by decide +kernel
lemma xminor_bits_151 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 151 := by decide +kernel
lemma xminor_bits_152 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 152 := by decide +kernel
lemma xminor_bits_153 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 153 := by decide +kernel
lemma xminor_bits_154 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 154 := by decide +kernel
lemma xminor_bits_155 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 155 := by decide +kernel
lemma xminor_bits_156 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 156 := by decide +kernel
lemma xminor_bits_157 : (fun i : Fin 158 => combination xImask (xMmask i) = unit i) 157 := by decide +kernel
lemma xminor_bits : ∀ i, combination xImask (xMmask i) = unit i := by
  intro i
  fin_cases i
  · exact xminor_bits_0
  · exact xminor_bits_1
  · exact xminor_bits_2
  · exact xminor_bits_3
  · exact xminor_bits_4
  · exact xminor_bits_5
  · exact xminor_bits_6
  · exact xminor_bits_7
  · exact xminor_bits_8
  · exact xminor_bits_9
  · exact xminor_bits_10
  · exact xminor_bits_11
  · exact xminor_bits_12
  · exact xminor_bits_13
  · exact xminor_bits_14
  · exact xminor_bits_15
  · exact xminor_bits_16
  · exact xminor_bits_17
  · exact xminor_bits_18
  · exact xminor_bits_19
  · exact xminor_bits_20
  · exact xminor_bits_21
  · exact xminor_bits_22
  · exact xminor_bits_23
  · exact xminor_bits_24
  · exact xminor_bits_25
  · exact xminor_bits_26
  · exact xminor_bits_27
  · exact xminor_bits_28
  · exact xminor_bits_29
  · exact xminor_bits_30
  · exact xminor_bits_31
  · exact xminor_bits_32
  · exact xminor_bits_33
  · exact xminor_bits_34
  · exact xminor_bits_35
  · exact xminor_bits_36
  · exact xminor_bits_37
  · exact xminor_bits_38
  · exact xminor_bits_39
  · exact xminor_bits_40
  · exact xminor_bits_41
  · exact xminor_bits_42
  · exact xminor_bits_43
  · exact xminor_bits_44
  · exact xminor_bits_45
  · exact xminor_bits_46
  · exact xminor_bits_47
  · exact xminor_bits_48
  · exact xminor_bits_49
  · exact xminor_bits_50
  · exact xminor_bits_51
  · exact xminor_bits_52
  · exact xminor_bits_53
  · exact xminor_bits_54
  · exact xminor_bits_55
  · exact xminor_bits_56
  · exact xminor_bits_57
  · exact xminor_bits_58
  · exact xminor_bits_59
  · exact xminor_bits_60
  · exact xminor_bits_61
  · exact xminor_bits_62
  · exact xminor_bits_63
  · exact xminor_bits_64
  · exact xminor_bits_65
  · exact xminor_bits_66
  · exact xminor_bits_67
  · exact xminor_bits_68
  · exact xminor_bits_69
  · exact xminor_bits_70
  · exact xminor_bits_71
  · exact xminor_bits_72
  · exact xminor_bits_73
  · exact xminor_bits_74
  · exact xminor_bits_75
  · exact xminor_bits_76
  · exact xminor_bits_77
  · exact xminor_bits_78
  · exact xminor_bits_79
  · exact xminor_bits_80
  · exact xminor_bits_81
  · exact xminor_bits_82
  · exact xminor_bits_83
  · exact xminor_bits_84
  · exact xminor_bits_85
  · exact xminor_bits_86
  · exact xminor_bits_87
  · exact xminor_bits_88
  · exact xminor_bits_89
  · exact xminor_bits_90
  · exact xminor_bits_91
  · exact xminor_bits_92
  · exact xminor_bits_93
  · exact xminor_bits_94
  · exact xminor_bits_95
  · exact xminor_bits_96
  · exact xminor_bits_97
  · exact xminor_bits_98
  · exact xminor_bits_99
  · exact xminor_bits_100
  · exact xminor_bits_101
  · exact xminor_bits_102
  · exact xminor_bits_103
  · exact xminor_bits_104
  · exact xminor_bits_105
  · exact xminor_bits_106
  · exact xminor_bits_107
  · exact xminor_bits_108
  · exact xminor_bits_109
  · exact xminor_bits_110
  · exact xminor_bits_111
  · exact xminor_bits_112
  · exact xminor_bits_113
  · exact xminor_bits_114
  · exact xminor_bits_115
  · exact xminor_bits_116
  · exact xminor_bits_117
  · exact xminor_bits_118
  · exact xminor_bits_119
  · exact xminor_bits_120
  · exact xminor_bits_121
  · exact xminor_bits_122
  · exact xminor_bits_123
  · exact xminor_bits_124
  · exact xminor_bits_125
  · exact xminor_bits_126
  · exact xminor_bits_127
  · exact xminor_bits_128
  · exact xminor_bits_129
  · exact xminor_bits_130
  · exact xminor_bits_131
  · exact xminor_bits_132
  · exact xminor_bits_133
  · exact xminor_bits_134
  · exact xminor_bits_135
  · exact xminor_bits_136
  · exact xminor_bits_137
  · exact xminor_bits_138
  · exact xminor_bits_139
  · exact xminor_bits_140
  · exact xminor_bits_141
  · exact xminor_bits_142
  · exact xminor_bits_143
  · exact xminor_bits_144
  · exact xminor_bits_145
  · exact xminor_bits_146
  · exact xminor_bits_147
  · exact xminor_bits_148
  · exact xminor_bits_149
  · exact xminor_bits_150
  · exact xminor_bits_151
  · exact xminor_bits_152
  · exact xminor_bits_153
  · exact xminor_bits_154
  · exact xminor_bits_155
  · exact xminor_bits_156
  · exact xminor_bits_157
lemma xM_bits (i j : Fin 158) : (xMmask i).getLsbD j.val = (xrow (xrows i)).getLsbD (xpiv j).val := by
  simp [xMmask, xpiv, BitVec.getLsbD_setWidth, j.isLt]
lemma xminor : (xH.submatrix xrows xpiv) * xInv = 1 := by
  have h := product xMmask xImask unit xminor_bits
  have hm : (Matrix.of fun i j => entry (xMmask i) j) = xH.submatrix xrows xpiv := by
    apply Matrix.ext
    intro i j
    change entry (xMmask i) j = xH (xrows i) (xpiv j)
    rw [← xrow_entry]
    unfold entry
    rw [xM_bits]
  have hu : (Matrix.of fun i j => entry (unit i) j) = (1 : Matrix (Fin 158) (Fin 158) (ZMod 2)) := by
    apply Matrix.ext; intro i j
    change entry (unit i) j = if i = j then 1 else 0
    rw [unit_entry]
    simp only [eq_comm]
  rw [hm,hu] at h
  exact h
lemma xrank : xH.rank = 158 := by
  apply Nat.le_antisymm
  · rw [xfactor]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)
  · have h := Matrix.rank_mul_le_left (xH.submatrix xrows xpiv) xInv
    rw [xminor,Matrix.rank_one,Fintype.card_fin] at h
    exact h.trans (Matrix.rank_submatrix_le _ _ _)
end BB336C2KernelData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336C2Cert BB336C2Bits
namespace BB336C2KernelData
def zv : Fin 336 → ZMod 2 := entry (BitVec.ofNat 336 53919944756514855329637707487990531375529917044637015664361447623683)
def zvsupport : List (Fin 336) := [0, 1, 10, 11, 18, 19, 90, 98, 164, 187, 205, 225]
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
def xv : Fin 336 → ZMod 2 := entry (BitVec.ofNat 336 2195794672926695564702201735176818422889160166785696940960862416339598498338075649464386342656933888)
def xvsupport : List (Fin 336) := [27, 47, 65, 168, 233, 234, 241, 242, 251, 256, 322, 330]
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
def zpair : Fin 336 → ZMod 2 := entry (BitVec.ofNat 336 18982007396359966101845)
def zpairsupport : List (Fin 336) := [0, 2, 4, 6, 8, 12, 16, 22, 24, 32, 42, 44, 46, 48, 50, 54, 58, 64, 66, 74]
lemma zpair_support : (Finset.univ.filter fun j => zpair j ≠ 0) = zpairsupport.toFinset := by decide +kernel
lemma zpair_sig : signature zmask zpairsupport = 0 := by decide +kernel
lemma zpair_kernel : zH *ᵥ zpair = 0 := by
  funext i
  change (zH *ᵥ zpair) i = 0
  rw [support_mul,zpair_support]
  change ∑ j ∈ zpairsupport.toFinset, entry (zmask j) i = 0
  rw [← signature_entry zmask zpairsupport (by decide +kernel) i,zpair_sig]
  simp [entry]
def xpair : Fin 336 → ZMod 2 := entry (BitVec.ofNat 336 2404791441587852051157634755269655177685667428964507729109017097484359434240)
def xpairsupport : List (Fin 336) := [168, 178, 186, 188, 194, 198, 202, 204, 206, 208, 210, 220, 228, 230, 236, 240, 244, 246, 248, 250]
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

end BB336C2KernelData


set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB336C2Cert BB336C2KernelData
namespace BB336C2Finish
private lemma lowerZ (v : Qubit 2 84 → ZMod 2) (hv : IsZLogical polyA polyB v) : 12 ≤ weight v := by
  by_contra hlt
  have hki : xH *ᵥ (v ∘ eqb) = 0 := by rw [← xtable]; exact index_kernel _ v hv.1
  have hd := kernel_even xH xcolParity (v ∘ eqb) hki
  rw [BB336C2KernelData.weight_equiv] at hd
  exact hv.2 (BBCode.new336_class2_small_kernel v hv.1 (by omega))
private lemma lowerX (v : Qubit 2 84 → ZMod 2) (hv : IsXLogical polyA polyB v) : 12 ≤ weight v := by
  have h := lowerZ (v ∘ BB336C2Symmetry.dualQ) (BB336C2Symmetry.x_to_z _ _ _ hv)
  rwa [BB336C2Symmetry.weight_equiv] at h

theorem complete :
    IsCode (l := 2) (m := 84) {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)} 336 20 12 := by
  change IsCode polyA polyB 336 20 12
  refine ⟨rfl,?_,?_,?_⟩
  · unfold NumLogical
    have hx : (HX polyA polyB).rank = 158 := by
      exact (Matrix.rank_submatrix (HX polyA polyB) er eqb).symm.trans
        ((congrArg Matrix.rank xtable).trans xrank)
    have hz : (HZ polyA polyB).rank = 158 :=
      ((congrArg Matrix.rank (BB336C2Symmetry.HX_dual polyA polyB)).symm.trans
        (Matrix.rank_submatrix (HX polyA polyB) BB336C2Symmetry.negG BB336C2Symmetry.dualQ)).trans hx
    exact congrArg₂ (fun a b : ℕ => a + b + 20) hx hz
  · refine ⟨⟨xv ∘ eqb.symm,xlogical,?_⟩,lowerX⟩
    rw [BB336C2KernelData.weight_equiv,xv_weight]
  · refine ⟨⟨zv ∘ eqb.symm,zlogical,?_⟩,lowerZ⟩
    rw [BB336C2KernelData.weight_equiv,zv_weight]
end BB336C2Finish

theorem solution : IsCode (l := 2) (m := 84) {(0, 0), (0, 1), (1, 5)} {(0, 0), (0,20), (0,46)} 336 20 12 := BB336C2Finish.complete
#print axioms solution
