-- Prove2me | solution 1 for BBCode.new336_class2_small_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:46:22.219636+00:00
-- url     : https://prove2.me/submissions/ee4afea5-0e6f-42d1-b9a8-6def3e80b227

import Definitions.Def_BBCode_Setting
import Theorems.Thm_BBCode_new336_class2_support_left_companion163
import Theorems.Thm_BBCode_new336_class2_support_left_companion164
import Theorems.Thm_BBCode_new336_class2_support_left_companion267
import Theorems.Thm_BBCode_new336_class2_support_left_companion293
import Theorems.Thm_BBCode_new336_class2_support_left_companion331
import Theorems.Thm_BBCode_new336_class2_support_right_companion64
import Theorems.Thm_BBCode_new336_class2_support_right_companion65
import Theorems.Thm_BBCode_new336_class2_support_right_companion153
import Theorems.Thm_BBCode_new336_class2_support_right_companion194
import Theorems.Thm_BBCode_new336_class2_support_right_companion232
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
open Matrix BBCode BB336C2Cert
namespace BB336C2Peel
lemma weight_sub_lt {a : Type} [Fintype a] (v u : a → ZMod 2) (anchor : a)
    (ha : u anchor ≠ 0) (hs : ∀ q, u q ≠ 0 → v q ≠ 0) : weight (v-u) < weight v := by
  classical
  let T := Finset.univ.filter fun q => v q ≠ 0
  let S := Finset.univ.filter fun q => u q ≠ 0
  have hST : S ⊆ T := by intro q hq; simpa [S,T] using hs q (by simpa [S] using hq)
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨anchor,by simpa [S] using ha⟩
  have he : (Finset.univ.filter fun q => (v-u) q ≠ 0) = T \ S := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,not_not,T,S,Pi.sub_apply]
    by_cases hu : u q = 0
    · simp [hu]
    · have hu1 := binary_eq_one hu
      have hv1 := binary_eq_one (hs q hu)
      simp [hu1,hv1]
  change (Finset.univ.filter fun q => (v-u) q ≠ 0).card < T.card
  rw [he,Finset.card_sdiff_of_subset hST]
  have hle := Finset.card_le_card hST
  omega
end BB336C2Peel

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB336C2Cert
namespace BB336C2Search

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
end BB336C2Search

set_option maxHeartbeats 0
open BB336C2Search
namespace BB336C2Count
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
end BB336C2Count

set_option maxHeartbeats 0
namespace BB336C2High

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
end BB336C2High

namespace BB336C2KernelData
open BB336C2Search
def xneighbors (i : Fin 168) : List (Fin 336) := (if i.val < 84 then (if i.val < 42 then (if i.val < 21 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [0, 1, 89, 168, 188, 214] else [1, 2, 90, 169, 189, 215]) else (if i.val < 3 then [2, 3, 91, 170, 190, 216] else (if i.val < 4 then [3, 4, 92, 171, 191, 217] else [4, 5, 93, 172, 192, 218]))) else (if i.val < 7 then (if i.val < 6 then [5, 6, 94, 173, 193, 219] else [6, 7, 95, 174, 194, 220]) else (if i.val < 8 then [7, 8, 96, 175, 195, 221] else (if i.val < 9 then [8, 9, 97, 176, 196, 222] else [9, 10, 98, 177, 197, 223])))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then [10, 11, 99, 178, 198, 224] else [11, 12, 100, 179, 199, 225]) else (if i.val < 13 then [12, 13, 101, 180, 200, 226] else (if i.val < 14 then [13, 14, 102, 181, 201, 227] else [14, 15, 103, 182, 202, 228]))) else (if i.val < 18 then (if i.val < 16 then [15, 16, 104, 183, 203, 229] else (if i.val < 17 then [16, 17, 105, 184, 204, 230] else [17, 18, 106, 185, 205, 231])) else (if i.val < 19 then [18, 19, 107, 186, 206, 232] else (if i.val < 20 then [19, 20, 108, 187, 207, 233] else [20, 21, 109, 188, 208, 234]))))) else (if i.val < 31 then (if i.val < 26 then (if i.val < 23 then (if i.val < 22 then [21, 22, 110, 189, 209, 235] else [22, 23, 111, 190, 210, 236]) else (if i.val < 24 then [23, 24, 112, 191, 211, 237] else (if i.val < 25 then [24, 25, 113, 192, 212, 238] else [25, 26, 114, 193, 213, 239]))) else (if i.val < 28 then (if i.val < 27 then [26, 27, 115, 194, 214, 240] else [27, 28, 116, 195, 215, 241]) else (if i.val < 29 then [28, 29, 117, 196, 216, 242] else (if i.val < 30 then [29, 30, 118, 197, 217, 243] else [30, 31, 119, 198, 218, 244])))) else (if i.val < 36 then (if i.val < 33 then (if i.val < 32 then [31, 32, 120, 199, 219, 245] else [32, 33, 121, 200, 220, 246]) else (if i.val < 34 then [33, 34, 122, 201, 221, 247] else (if i.val < 35 then [34, 35, 123, 202, 222, 248] else [35, 36, 124, 203, 223, 249]))) else (if i.val < 39 then (if i.val < 37 then [36, 37, 125, 204, 224, 250] else (if i.val < 38 then [37, 38, 126, 205, 225, 251] else [38, 39, 127, 168, 206, 226])) else (if i.val < 40 then [39, 40, 128, 169, 207, 227] else (if i.val < 41 then [40, 41, 129, 170, 208, 228] else [41, 42, 130, 171, 209, 229])))))) else (if i.val < 63 then (if i.val < 52 then (if i.val < 47 then (if i.val < 44 then (if i.val < 43 then [42, 43, 131, 172, 210, 230] else [43, 44, 132, 173, 211, 231]) else (if i.val < 45 then [44, 45, 133, 174, 212, 232] else (if i.val < 46 then [45, 46, 134, 175, 213, 233] else [46, 47, 135, 176, 214, 234]))) else (if i.val < 49 then (if i.val < 48 then [47, 48, 136, 177, 215, 235] else [48, 49, 137, 178, 216, 236]) else (if i.val < 50 then [49, 50, 138, 179, 217, 237] else (if i.val < 51 then [50, 51, 139, 180, 218, 238] else [51, 52, 140, 181, 219, 239])))) else (if i.val < 57 then (if i.val < 54 then (if i.val < 53 then [52, 53, 141, 182, 220, 240] else [53, 54, 142, 183, 221, 241]) else (if i.val < 55 then [54, 55, 143, 184, 222, 242] else (if i.val < 56 then [55, 56, 144, 185, 223, 243] else [56, 57, 145, 186, 224, 244]))) else (if i.val < 60 then (if i.val < 58 then [57, 58, 146, 187, 225, 245] else (if i.val < 59 then [58, 59, 147, 188, 226, 246] else [59, 60, 148, 189, 227, 247])) else (if i.val < 61 then [60, 61, 149, 190, 228, 248] else (if i.val < 62 then [61, 62, 150, 191, 229, 249] else [62, 63, 151, 192, 230, 250]))))) else (if i.val < 73 then (if i.val < 68 then (if i.val < 65 then (if i.val < 64 then [63, 64, 152, 193, 231, 251] else [64, 65, 153, 168, 194, 232]) else (if i.val < 66 then [65, 66, 154, 169, 195, 233] else (if i.val < 67 then [66, 67, 155, 170, 196, 234] else [67, 68, 156, 171, 197, 235]))) else (if i.val < 70 then (if i.val < 69 then [68, 69, 157, 172, 198, 236] else [69, 70, 158, 173, 199, 237]) else (if i.val < 71 then [70, 71, 159, 174, 200, 238] else (if i.val < 72 then [71, 72, 160, 175, 201, 239] else [72, 73, 161, 176, 202, 240])))) else (if i.val < 78 then (if i.val < 75 then (if i.val < 74 then [73, 74, 162, 177, 203, 241] else [74, 75, 163, 178, 204, 242]) else (if i.val < 76 then [75, 76, 164, 179, 205, 243] else (if i.val < 77 then [76, 77, 165, 180, 206, 244] else [77, 78, 166, 181, 207, 245]))) else (if i.val < 81 then (if i.val < 79 then [78, 79, 167, 182, 208, 246] else (if i.val < 80 then [79, 80, 84, 183, 209, 247] else [80, 81, 85, 184, 210, 248])) else (if i.val < 82 then [81, 82, 86, 185, 211, 249] else (if i.val < 83 then [82, 83, 87, 186, 212, 250] else [0, 83, 88, 187, 213, 251]))))))) else (if i.val < 126 then (if i.val < 105 then (if i.val < 94 then (if i.val < 89 then (if i.val < 86 then (if i.val < 85 then [5, 84, 85, 252, 272, 298] else [6, 85, 86, 253, 273, 299]) else (if i.val < 87 then [7, 86, 87, 254, 274, 300] else (if i.val < 88 then [8, 87, 88, 255, 275, 301] else [9, 88, 89, 256, 276, 302]))) else (if i.val < 91 then (if i.val < 90 then [10, 89, 90, 257, 277, 303] else [11, 90, 91, 258, 278, 304]) else (if i.val < 92 then [12, 91, 92, 259, 279, 305] else (if i.val < 93 then [13, 92, 93, 260, 280, 306] else [14, 93, 94, 261, 281, 307])))) else (if i.val < 99 then (if i.val < 96 then (if i.val < 95 then [15, 94, 95, 262, 282, 308] else [16, 95, 96, 263, 283, 309]) else (if i.val < 97 then [17, 96, 97, 264, 284, 310] else (if i.val < 98 then [18, 97, 98, 265, 285, 311] else [19, 98, 99, 266, 286, 312]))) else (if i.val < 102 then (if i.val < 100 then [20, 99, 100, 267, 287, 313] else (if i.val < 101 then [21, 100, 101, 268, 288, 314] else [22, 101, 102, 269, 289, 315])) else (if i.val < 103 then [23, 102, 103, 270, 290, 316] else (if i.val < 104 then [24, 103, 104, 271, 291, 317] else [25, 104, 105, 272, 292, 318]))))) else (if i.val < 115 then (if i.val < 110 then (if i.val < 107 then (if i.val < 106 then [26, 105, 106, 273, 293, 319] else [27, 106, 107, 274, 294, 320]) else (if i.val < 108 then [28, 107, 108, 275, 295, 321] else (if i.val < 109 then [29, 108, 109, 276, 296, 322] else [30, 109, 110, 277, 297, 323]))) else (if i.val < 112 then (if i.val < 111 then [31, 110, 111, 278, 298, 324] else [32, 111, 112, 279, 299, 325]) else (if i.val < 113 then [33, 112, 113, 280, 300, 326] else (if i.val < 114 then [34, 113, 114, 281, 301, 327] else [35, 114, 115, 282, 302, 328])))) else (if i.val < 120 then (if i.val < 117 then (if i.val < 116 then [36, 115, 116, 283, 303, 329] else [37, 116, 117, 284, 304, 330]) else (if i.val < 118 then [38, 117, 118, 285, 305, 331] else (if i.val < 119 then [39, 118, 119, 286, 306, 332] else [40, 119, 120, 287, 307, 333]))) else (if i.val < 123 then (if i.val < 121 then [41, 120, 121, 288, 308, 334] else (if i.val < 122 then [42, 121, 122, 289, 309, 335] else [43, 122, 123, 252, 290, 310])) else (if i.val < 124 then [44, 123, 124, 253, 291, 311] else (if i.val < 125 then [45, 124, 125, 254, 292, 312] else [46, 125, 126, 255, 293, 313])))))) else (if i.val < 147 then (if i.val < 136 then (if i.val < 131 then (if i.val < 128 then (if i.val < 127 then [47, 126, 127, 256, 294, 314] else [48, 127, 128, 257, 295, 315]) else (if i.val < 129 then [49, 128, 129, 258, 296, 316] else (if i.val < 130 then [50, 129, 130, 259, 297, 317] else [51, 130, 131, 260, 298, 318]))) else (if i.val < 133 then (if i.val < 132 then [52, 131, 132, 261, 299, 319] else [53, 132, 133, 262, 300, 320]) else (if i.val < 134 then [54, 133, 134, 263, 301, 321] else (if i.val < 135 then [55, 134, 135, 264, 302, 322] else [56, 135, 136, 265, 303, 323])))) else (if i.val < 141 then (if i.val < 138 then (if i.val < 137 then [57, 136, 137, 266, 304, 324] else [58, 137, 138, 267, 305, 325]) else (if i.val < 139 then [59, 138, 139, 268, 306, 326] else (if i.val < 140 then [60, 139, 140, 269, 307, 327] else [61, 140, 141, 270, 308, 328]))) else (if i.val < 144 then (if i.val < 142 then [62, 141, 142, 271, 309, 329] else (if i.val < 143 then [63, 142, 143, 272, 310, 330] else [64, 143, 144, 273, 311, 331])) else (if i.val < 145 then [65, 144, 145, 274, 312, 332] else (if i.val < 146 then [66, 145, 146, 275, 313, 333] else [67, 146, 147, 276, 314, 334]))))) else (if i.val < 157 then (if i.val < 152 then (if i.val < 149 then (if i.val < 148 then [68, 147, 148, 277, 315, 335] else [69, 148, 149, 252, 278, 316]) else (if i.val < 150 then [70, 149, 150, 253, 279, 317] else (if i.val < 151 then [71, 150, 151, 254, 280, 318] else [72, 151, 152, 255, 281, 319]))) else (if i.val < 154 then (if i.val < 153 then [73, 152, 153, 256, 282, 320] else [74, 153, 154, 257, 283, 321]) else (if i.val < 155 then [75, 154, 155, 258, 284, 322] else (if i.val < 156 then [76, 155, 156, 259, 285, 323] else [77, 156, 157, 260, 286, 324])))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then [78, 157, 158, 261, 287, 325] else [79, 158, 159, 262, 288, 326]) else (if i.val < 160 then [80, 159, 160, 263, 289, 327] else (if i.val < 161 then [81, 160, 161, 264, 290, 328] else [82, 161, 162, 265, 291, 329]))) else (if i.val < 165 then (if i.val < 163 then [83, 162, 163, 266, 292, 330] else (if i.val < 164 then [0, 163, 164, 267, 293, 331] else [1, 164, 165, 268, 294, 332])) else (if i.val < 166 then [2, 165, 166, 269, 295, 333] else (if i.val < 167 then [3, 166, 167, 270, 296, 334] else [4, 84, 167, 271, 297, 335]))))))))
def xpos (j : Fin 336) : List (Fin 168) := (if j.val < 168 then (if j.val < 84 then (if j.val < 42 then (if j.val < 21 then (if j.val < 10 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [0, 83, 163] else [0, 1, 164]) else (if j.val < 3 then [1, 2, 165] else (if j.val < 4 then [2, 3, 166] else [3, 4, 167]))) else (if j.val < 7 then (if j.val < 6 then [4, 5, 84] else [5, 6, 85]) else (if j.val < 8 then [6, 7, 86] else (if j.val < 9 then [7, 8, 87] else [8, 9, 88])))) else (if j.val < 15 then (if j.val < 12 then (if j.val < 11 then [9, 10, 89] else [10, 11, 90]) else (if j.val < 13 then [11, 12, 91] else (if j.val < 14 then [12, 13, 92] else [13, 14, 93]))) else (if j.val < 18 then (if j.val < 16 then [14, 15, 94] else (if j.val < 17 then [15, 16, 95] else [16, 17, 96])) else (if j.val < 19 then [17, 18, 97] else (if j.val < 20 then [18, 19, 98] else [19, 20, 99]))))) else (if j.val < 31 then (if j.val < 26 then (if j.val < 23 then (if j.val < 22 then [20, 21, 100] else [21, 22, 101]) else (if j.val < 24 then [22, 23, 102] else (if j.val < 25 then [23, 24, 103] else [24, 25, 104]))) else (if j.val < 28 then (if j.val < 27 then [25, 26, 105] else [26, 27, 106]) else (if j.val < 29 then [27, 28, 107] else (if j.val < 30 then [28, 29, 108] else [29, 30, 109])))) else (if j.val < 36 then (if j.val < 33 then (if j.val < 32 then [30, 31, 110] else [31, 32, 111]) else (if j.val < 34 then [32, 33, 112] else (if j.val < 35 then [33, 34, 113] else [34, 35, 114]))) else (if j.val < 39 then (if j.val < 37 then [35, 36, 115] else (if j.val < 38 then [36, 37, 116] else [37, 38, 117])) else (if j.val < 40 then [38, 39, 118] else (if j.val < 41 then [39, 40, 119] else [40, 41, 120])))))) else (if j.val < 63 then (if j.val < 52 then (if j.val < 47 then (if j.val < 44 then (if j.val < 43 then [41, 42, 121] else [42, 43, 122]) else (if j.val < 45 then [43, 44, 123] else (if j.val < 46 then [44, 45, 124] else [45, 46, 125]))) else (if j.val < 49 then (if j.val < 48 then [46, 47, 126] else [47, 48, 127]) else (if j.val < 50 then [48, 49, 128] else (if j.val < 51 then [49, 50, 129] else [50, 51, 130])))) else (if j.val < 57 then (if j.val < 54 then (if j.val < 53 then [51, 52, 131] else [52, 53, 132]) else (if j.val < 55 then [53, 54, 133] else (if j.val < 56 then [54, 55, 134] else [55, 56, 135]))) else (if j.val < 60 then (if j.val < 58 then [56, 57, 136] else (if j.val < 59 then [57, 58, 137] else [58, 59, 138])) else (if j.val < 61 then [59, 60, 139] else (if j.val < 62 then [60, 61, 140] else [61, 62, 141]))))) else (if j.val < 73 then (if j.val < 68 then (if j.val < 65 then (if j.val < 64 then [62, 63, 142] else [63, 64, 143]) else (if j.val < 66 then [64, 65, 144] else (if j.val < 67 then [65, 66, 145] else [66, 67, 146]))) else (if j.val < 70 then (if j.val < 69 then [67, 68, 147] else [68, 69, 148]) else (if j.val < 71 then [69, 70, 149] else (if j.val < 72 then [70, 71, 150] else [71, 72, 151])))) else (if j.val < 78 then (if j.val < 75 then (if j.val < 74 then [72, 73, 152] else [73, 74, 153]) else (if j.val < 76 then [74, 75, 154] else (if j.val < 77 then [75, 76, 155] else [76, 77, 156]))) else (if j.val < 81 then (if j.val < 79 then [77, 78, 157] else (if j.val < 80 then [78, 79, 158] else [79, 80, 159])) else (if j.val < 82 then [80, 81, 160] else (if j.val < 83 then [81, 82, 161] else [82, 83, 162]))))))) else (if j.val < 126 then (if j.val < 105 then (if j.val < 94 then (if j.val < 89 then (if j.val < 86 then (if j.val < 85 then [79, 84, 167] else [80, 84, 85]) else (if j.val < 87 then [81, 85, 86] else (if j.val < 88 then [82, 86, 87] else [83, 87, 88]))) else (if j.val < 91 then (if j.val < 90 then [0, 88, 89] else [1, 89, 90]) else (if j.val < 92 then [2, 90, 91] else (if j.val < 93 then [3, 91, 92] else [4, 92, 93])))) else (if j.val < 99 then (if j.val < 96 then (if j.val < 95 then [5, 93, 94] else [6, 94, 95]) else (if j.val < 97 then [7, 95, 96] else (if j.val < 98 then [8, 96, 97] else [9, 97, 98]))) else (if j.val < 102 then (if j.val < 100 then [10, 98, 99] else (if j.val < 101 then [11, 99, 100] else [12, 100, 101])) else (if j.val < 103 then [13, 101, 102] else (if j.val < 104 then [14, 102, 103] else [15, 103, 104]))))) else (if j.val < 115 then (if j.val < 110 then (if j.val < 107 then (if j.val < 106 then [16, 104, 105] else [17, 105, 106]) else (if j.val < 108 then [18, 106, 107] else (if j.val < 109 then [19, 107, 108] else [20, 108, 109]))) else (if j.val < 112 then (if j.val < 111 then [21, 109, 110] else [22, 110, 111]) else (if j.val < 113 then [23, 111, 112] else (if j.val < 114 then [24, 112, 113] else [25, 113, 114])))) else (if j.val < 120 then (if j.val < 117 then (if j.val < 116 then [26, 114, 115] else [27, 115, 116]) else (if j.val < 118 then [28, 116, 117] else (if j.val < 119 then [29, 117, 118] else [30, 118, 119]))) else (if j.val < 123 then (if j.val < 121 then [31, 119, 120] else (if j.val < 122 then [32, 120, 121] else [33, 121, 122])) else (if j.val < 124 then [34, 122, 123] else (if j.val < 125 then [35, 123, 124] else [36, 124, 125])))))) else (if j.val < 147 then (if j.val < 136 then (if j.val < 131 then (if j.val < 128 then (if j.val < 127 then [37, 125, 126] else [38, 126, 127]) else (if j.val < 129 then [39, 127, 128] else (if j.val < 130 then [40, 128, 129] else [41, 129, 130]))) else (if j.val < 133 then (if j.val < 132 then [42, 130, 131] else [43, 131, 132]) else (if j.val < 134 then [44, 132, 133] else (if j.val < 135 then [45, 133, 134] else [46, 134, 135])))) else (if j.val < 141 then (if j.val < 138 then (if j.val < 137 then [47, 135, 136] else [48, 136, 137]) else (if j.val < 139 then [49, 137, 138] else (if j.val < 140 then [50, 138, 139] else [51, 139, 140]))) else (if j.val < 144 then (if j.val < 142 then [52, 140, 141] else (if j.val < 143 then [53, 141, 142] else [54, 142, 143])) else (if j.val < 145 then [55, 143, 144] else (if j.val < 146 then [56, 144, 145] else [57, 145, 146]))))) else (if j.val < 157 then (if j.val < 152 then (if j.val < 149 then (if j.val < 148 then [58, 146, 147] else [59, 147, 148]) else (if j.val < 150 then [60, 148, 149] else (if j.val < 151 then [61, 149, 150] else [62, 150, 151]))) else (if j.val < 154 then (if j.val < 153 then [63, 151, 152] else [64, 152, 153]) else (if j.val < 155 then [65, 153, 154] else (if j.val < 156 then [66, 154, 155] else [67, 155, 156])))) else (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then [68, 156, 157] else [69, 157, 158]) else (if j.val < 160 then [70, 158, 159] else (if j.val < 161 then [71, 159, 160] else [72, 160, 161]))) else (if j.val < 165 then (if j.val < 163 then [73, 161, 162] else (if j.val < 164 then [74, 162, 163] else [75, 163, 164])) else (if j.val < 166 then [76, 164, 165] else (if j.val < 167 then [77, 165, 166] else [78, 166, 167])))))))) else (if j.val < 252 then (if j.val < 210 then (if j.val < 189 then (if j.val < 178 then (if j.val < 173 then (if j.val < 170 then (if j.val < 169 then [0, 38, 64] else [1, 39, 65]) else (if j.val < 171 then [2, 40, 66] else (if j.val < 172 then [3, 41, 67] else [4, 42, 68]))) else (if j.val < 175 then (if j.val < 174 then [5, 43, 69] else [6, 44, 70]) else (if j.val < 176 then [7, 45, 71] else (if j.val < 177 then [8, 46, 72] else [9, 47, 73])))) else (if j.val < 183 then (if j.val < 180 then (if j.val < 179 then [10, 48, 74] else [11, 49, 75]) else (if j.val < 181 then [12, 50, 76] else (if j.val < 182 then [13, 51, 77] else [14, 52, 78]))) else (if j.val < 186 then (if j.val < 184 then [15, 53, 79] else (if j.val < 185 then [16, 54, 80] else [17, 55, 81])) else (if j.val < 187 then [18, 56, 82] else (if j.val < 188 then [19, 57, 83] else [0, 20, 58]))))) else (if j.val < 199 then (if j.val < 194 then (if j.val < 191 then (if j.val < 190 then [1, 21, 59] else [2, 22, 60]) else (if j.val < 192 then [3, 23, 61] else (if j.val < 193 then [4, 24, 62] else [5, 25, 63]))) else (if j.val < 196 then (if j.val < 195 then [6, 26, 64] else [7, 27, 65]) else (if j.val < 197 then [8, 28, 66] else (if j.val < 198 then [9, 29, 67] else [10, 30, 68])))) else (if j.val < 204 then (if j.val < 201 then (if j.val < 200 then [11, 31, 69] else [12, 32, 70]) else (if j.val < 202 then [13, 33, 71] else (if j.val < 203 then [14, 34, 72] else [15, 35, 73]))) else (if j.val < 207 then (if j.val < 205 then [16, 36, 74] else (if j.val < 206 then [17, 37, 75] else [18, 38, 76])) else (if j.val < 208 then [19, 39, 77] else (if j.val < 209 then [20, 40, 78] else [21, 41, 79])))))) else (if j.val < 231 then (if j.val < 220 then (if j.val < 215 then (if j.val < 212 then (if j.val < 211 then [22, 42, 80] else [23, 43, 81]) else (if j.val < 213 then [24, 44, 82] else (if j.val < 214 then [25, 45, 83] else [0, 26, 46]))) else (if j.val < 217 then (if j.val < 216 then [1, 27, 47] else [2, 28, 48]) else (if j.val < 218 then [3, 29, 49] else (if j.val < 219 then [4, 30, 50] else [5, 31, 51])))) else (if j.val < 225 then (if j.val < 222 then (if j.val < 221 then [6, 32, 52] else [7, 33, 53]) else (if j.val < 223 then [8, 34, 54] else (if j.val < 224 then [9, 35, 55] else [10, 36, 56]))) else (if j.val < 228 then (if j.val < 226 then [11, 37, 57] else (if j.val < 227 then [12, 38, 58] else [13, 39, 59])) else (if j.val < 229 then [14, 40, 60] else (if j.val < 230 then [15, 41, 61] else [16, 42, 62]))))) else (if j.val < 241 then (if j.val < 236 then (if j.val < 233 then (if j.val < 232 then [17, 43, 63] else [18, 44, 64]) else (if j.val < 234 then [19, 45, 65] else (if j.val < 235 then [20, 46, 66] else [21, 47, 67]))) else (if j.val < 238 then (if j.val < 237 then [22, 48, 68] else [23, 49, 69]) else (if j.val < 239 then [24, 50, 70] else (if j.val < 240 then [25, 51, 71] else [26, 52, 72])))) else (if j.val < 246 then (if j.val < 243 then (if j.val < 242 then [27, 53, 73] else [28, 54, 74]) else (if j.val < 244 then [29, 55, 75] else (if j.val < 245 then [30, 56, 76] else [31, 57, 77]))) else (if j.val < 249 then (if j.val < 247 then [32, 58, 78] else (if j.val < 248 then [33, 59, 79] else [34, 60, 80])) else (if j.val < 250 then [35, 61, 81] else (if j.val < 251 then [36, 62, 82] else [37, 63, 83]))))))) else (if j.val < 294 then (if j.val < 273 then (if j.val < 262 then (if j.val < 257 then (if j.val < 254 then (if j.val < 253 then [84, 122, 148] else [85, 123, 149]) else (if j.val < 255 then [86, 124, 150] else (if j.val < 256 then [87, 125, 151] else [88, 126, 152]))) else (if j.val < 259 then (if j.val < 258 then [89, 127, 153] else [90, 128, 154]) else (if j.val < 260 then [91, 129, 155] else (if j.val < 261 then [92, 130, 156] else [93, 131, 157])))) else (if j.val < 267 then (if j.val < 264 then (if j.val < 263 then [94, 132, 158] else [95, 133, 159]) else (if j.val < 265 then [96, 134, 160] else (if j.val < 266 then [97, 135, 161] else [98, 136, 162]))) else (if j.val < 270 then (if j.val < 268 then [99, 137, 163] else (if j.val < 269 then [100, 138, 164] else [101, 139, 165])) else (if j.val < 271 then [102, 140, 166] else (if j.val < 272 then [103, 141, 167] else [84, 104, 142]))))) else (if j.val < 283 then (if j.val < 278 then (if j.val < 275 then (if j.val < 274 then [85, 105, 143] else [86, 106, 144]) else (if j.val < 276 then [87, 107, 145] else (if j.val < 277 then [88, 108, 146] else [89, 109, 147]))) else (if j.val < 280 then (if j.val < 279 then [90, 110, 148] else [91, 111, 149]) else (if j.val < 281 then [92, 112, 150] else (if j.val < 282 then [93, 113, 151] else [94, 114, 152])))) else (if j.val < 288 then (if j.val < 285 then (if j.val < 284 then [95, 115, 153] else [96, 116, 154]) else (if j.val < 286 then [97, 117, 155] else (if j.val < 287 then [98, 118, 156] else [99, 119, 157]))) else (if j.val < 291 then (if j.val < 289 then [100, 120, 158] else (if j.val < 290 then [101, 121, 159] else [102, 122, 160])) else (if j.val < 292 then [103, 123, 161] else (if j.val < 293 then [104, 124, 162] else [105, 125, 163])))))) else (if j.val < 315 then (if j.val < 304 then (if j.val < 299 then (if j.val < 296 then (if j.val < 295 then [106, 126, 164] else [107, 127, 165]) else (if j.val < 297 then [108, 128, 166] else (if j.val < 298 then [109, 129, 167] else [84, 110, 130]))) else (if j.val < 301 then (if j.val < 300 then [85, 111, 131] else [86, 112, 132]) else (if j.val < 302 then [87, 113, 133] else (if j.val < 303 then [88, 114, 134] else [89, 115, 135])))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 305 then [90, 116, 136] else [91, 117, 137]) else (if j.val < 307 then [92, 118, 138] else (if j.val < 308 then [93, 119, 139] else [94, 120, 140]))) else (if j.val < 312 then (if j.val < 310 then [95, 121, 141] else (if j.val < 311 then [96, 122, 142] else [97, 123, 143])) else (if j.val < 313 then [98, 124, 144] else (if j.val < 314 then [99, 125, 145] else [100, 126, 146]))))) else (if j.val < 325 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then [101, 127, 147] else [102, 128, 148]) else (if j.val < 318 then [103, 129, 149] else (if j.val < 319 then [104, 130, 150] else [105, 131, 151]))) else (if j.val < 322 then (if j.val < 321 then [106, 132, 152] else [107, 133, 153]) else (if j.val < 323 then [108, 134, 154] else (if j.val < 324 then [109, 135, 155] else [110, 136, 156])))) else (if j.val < 330 then (if j.val < 327 then (if j.val < 326 then [111, 137, 157] else [112, 138, 158]) else (if j.val < 328 then [113, 139, 159] else (if j.val < 329 then [114, 140, 160] else [115, 141, 161]))) else (if j.val < 333 then (if j.val < 331 then [116, 142, 162] else (if j.val < 332 then [117, 143, 163] else [118, 144, 164])) else (if j.val < 334 then [119, 145, 165] else (if j.val < 335 then [120, 146, 166] else [121, 147, 167])))))))))
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
  BB336C2Count.update_eq (xmask j) sy (xpos j) (xpos_spec j).1 (xpos_spec j).2 (xthree j)
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

end BB336C2KernelData

namespace BB336C2KernelData
lemma xnonzero : ∀ j, xmask j ≠ 0 := by decide +kernel
end BB336C2KernelData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BB336C2Cert BB336C2KernelData
namespace BB336C2Peel
section
variable (left : ∀ (v : Qubit 2 84 → ZMod 2), HX polyA polyB *ᵥ v = 0 → weight v ≤ 10 →
    v (Sum.inl (0,0)) ≠ 0 → ∃ u : Qubit 2 84 → ZMod 2,
      HX polyA polyB *ᵥ u = 0 ∧ u ∈ rowSpace (HZ polyA polyB) ∧
      u (Sum.inl (0,0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0)
variable (right : ∀ (v : Qubit 2 84 → ZMod 2), HX polyA polyB *ᵥ v = 0 → weight v ≤ 10 →
    v (Sum.inr (0,0)) ≠ 0 → ∃ u : Qubit 2 84 → ZMod 2,
      HX polyA polyB *ᵥ u = 0 ∧ u ∈ rowSpace (HZ polyA polyB) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0)
include left right
lemma close (v : Qubit 2 84 → ZMod 2) (hv : HX polyA polyB *ᵥ v = 0)
    (hw : weight v ≤ 10) : v ∈ rowSpace (HZ polyA polyB) := by
  classical
  induction hwt : weight v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hzero : v = 0
    · subst v; exact Submodule.zero_mem _
    have hex : ∃ q, v q ≠ 0 := by
      by_contra hn
      apply hzero
      funext q
      by_contra hq
      exact hn ⟨q,hq⟩
    obtain ⟨q,hq⟩ := hex
    suffices ∀ g : Grp 2 84, (v (Sum.inl g) ≠ 0 ∨ v (Sum.inr g) ≠ 0) →
        v ∈ rowSpace (HZ polyA polyB) by
      cases q with
      | inl g => exact this g (Or.inl hq)
      | inr g => exact this g (Or.inr hq)
    intro g ha
    let w := v ∘ BB336C2Symmetry.shiftQ g
    have hwker : HX polyA polyB *ᵥ w = 0 := by
      have h := BB336C2Symmetry.kernel_reindex (HX polyA polyB)
        (BB336C2Symmetry.shiftG g) (BB336C2Symmetry.shiftQ g) v hv
      rwa [BB336C2Symmetry.HX_shift] at h
    have hweq : weight w = weight v := BB336C2Symmetry.weight_equiv _ v
    have hwW : weight w ≤ 10 := by omega
    have hwr : w ∈ rowSpace (HZ polyA polyB) := by
      have peel : ∀ (anchor : Qubit 2 84) (u : Qubit 2 84 → ZMod 2),
          HX polyA polyB *ᵥ u = 0 → u ∈ rowSpace (HZ polyA polyB) →
          u anchor ≠ 0 → (∀ q, u q ≠ 0 → w q ≠ 0) → w ∈ rowSpace (HZ polyA polyB) := by
        intro anchor u huk hum hua hus
        have hless := weight_sub_lt w u anchor hua hus
        have hresker : HX polyA polyB *ᵥ (w-u) = 0 := by
          rw [Matrix.mulVec_sub,hwker,huk,sub_self]
        have hres := ih (weight (w-u)) (by omega) (w-u) hresker (by omega) rfl
        have hh := Submodule.add_mem (rowSpace (HZ polyA polyB)) hres hum
        simpa only [sub_add_cancel] using hh
      rcases ha with ha | ha
      · have hanchor : w (Sum.inl (0,0)) ≠ 0 := by
          change v (Sum.inl ((0 : Grp 2 84) + g)) ≠ 0
          simpa only [zero_add] using ha
        obtain ⟨u,huk,hum,hua,hus⟩ := left w hwker hwW hanchor
        exact peel (Sum.inl (0,0)) u huk hum hua hus
      · have hanchor : w (Sum.inr (0,0)) ≠ 0 := by
          change v (Sum.inr ((0 : Grp 2 84) + g)) ≠ 0
          simpa only [zero_add] using ha
        obtain ⟨u,huk,hum,hua,hus⟩ := right w hwker hwW hanchor
        exact peel (Sum.inr (0,0)) u huk hum hua hus
    have he := rowspace_reindex (HZ polyA polyB)
      (BB336C2Symmetry.shiftG g) (BB336C2Symmetry.shiftQ g) v
    rw [BB336C2Symmetry.HZ_shift] at he
    exact he.mp hwr
end
end BB336C2Peel

open Matrix BBCode BB336C2Cert BB336C2KernelData BB336C2Search
namespace BB336C2Other
lemma exists_other (anchor : Fin 336) (v : Fin 336 → ZMod 2)
    (ha : v anchor ≠ 0) (hv : xH *ᵥ v = 0) :
    ∃ j ∈ xneighbors (BB336C2High.pick (xmask anchor)), j ≠ anchor ∧ v j ≠ 0 := by
  classical
  let T := Finset.univ.filter fun j => v j ≠ 0
  let i := BB336C2High.pick (xmask anchor)
  have hp : entry (xmask anchor) i = 1 := by
    simp [entry,i,BB336C2High.pick_spec _ (xnonzero anchor)]
  have hT : ∑ j ∈ T, entry (xmask j) i = 0 := by
    change ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), xH i j = 0
    rw [← support_mul xH v i,hv]
    rfl
  have hu : ({anchor} : Finset (Fin 336)) ⊆ T := by simpa [T] using ha
  have hex : ∃ j ∈ T, j ≠ anchor ∧ entry (xmask j) i = 1 := by
    by_contra hnot
    have he : ∑ j ∈ ({anchor} : Finset (Fin 336)), entry (xmask j) i = ∑ j ∈ T, entry (xmask j) i := by
      apply Finset.sum_subset hu
      intro j hj hjn
      by_contra hne
      exact hnot ⟨j,hj,by simpa using hjn,binary_eq_one hne⟩
    simp only [Finset.sum_singleton,hT,hp] at he
    exact one_ne_zero he
  obtain ⟨j,hj,hne,hji⟩ := hex
  exact ⟨j,xcover i j hji,hne,by simpa [T] using hj⟩
end BB336C2Other

namespace BB336C2DistanceReduce
lemma complete (v : Qubit 2 84 → ZMod 2) (hv : HX polyA polyB *ᵥ v = 0)
    (hw : weight v ≤ 10) : v ∈ rowSpace (HZ polyA polyB) := by
  apply BB336C2Peel.close ?_ ?_ v hv hw
  · intro w hwker hwW haW
    have hwi : xH *ᵥ (w ∘ eqb) = 0 := by
      rw [← xtable]
      exact index_kernel _ w hwker
    have hanchor : (w ∘ eqb) 0 ≠ 0 := by
      simpa only [Function.comp_apply,show eqb (0 : Fin 336) = (Sum.inl (0,0)) from by decide +kernel] using haW
    obtain ⟨j,hj,hne,hvj⟩ := BB336C2Other.exists_other 0 (w ∘ eqb) hanchor hwi
    have hn : xneighbors (BB336C2High.pick (xmask (0 : Fin 336))) = [0, 163, 164, 267, 293, 331] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hne rfl)
    · apply BBCode.new336_class2_support_left_companion163 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (163 : Fin 336) = (Sum.inl (1,79)) from by decide +kernel] using hvj
    · apply BBCode.new336_class2_support_left_companion164 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (164 : Fin 336) = (Sum.inl (1,80)) from by decide +kernel] using hvj
    · apply BBCode.new336_class2_support_left_companion267 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (267 : Fin 336) = (Sum.inr (1,15)) from by decide +kernel] using hvj
    · apply BBCode.new336_class2_support_left_companion293 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (293 : Fin 336) = (Sum.inr (1,41)) from by decide +kernel] using hvj
    · apply BBCode.new336_class2_support_left_companion331 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (331 : Fin 336) = (Sum.inr (1,79)) from by decide +kernel] using hvj
  · intro w hwker hwW haW
    have hwi : xH *ᵥ (w ∘ eqb) = 0 := by
      rw [← xtable]
      exact index_kernel _ w hwker
    have hanchor : (w ∘ eqb) 168 ≠ 0 := by
      simpa only [Function.comp_apply,show eqb (168 : Fin 336) = (Sum.inr (0,0)) from by decide +kernel] using haW
    obtain ⟨j,hj,hne,hvj⟩ := BB336C2Other.exists_other 168 (w ∘ eqb) hanchor hwi
    have hn : xneighbors (BB336C2High.pick (xmask (168 : Fin 336))) = [64, 65, 153, 168, 194, 232] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · apply BBCode.new336_class2_support_right_companion64 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (64 : Fin 336) = (Sum.inl (0,64)) from by decide +kernel] using hvj
    · apply BBCode.new336_class2_support_right_companion65 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (65 : Fin 336) = (Sum.inl (0,65)) from by decide +kernel] using hvj
    · apply BBCode.new336_class2_support_right_companion153 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (153 : Fin 336) = (Sum.inl (1,69)) from by decide +kernel] using hvj
    · exact False.elim (hne rfl)
    · apply BBCode.new336_class2_support_right_companion194 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (194 : Fin 336) = (Sum.inr (0,26)) from by decide +kernel] using hvj
    · apply BBCode.new336_class2_support_right_companion232 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (232 : Fin 336) = (Sum.inr (0,64)) from by decide +kernel] using hvj
end BB336C2DistanceReduce
theorem solution (v : BBCode.Qubit 2 84 → ZMod 2)
    (hv : BBCode.HX (l := 2) (m := 84) {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10) :
    v ∈ BBCode.rowSpace (BBCode.HZ (l := 2) (m := 84)
      {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)}) := BB336C2DistanceReduce.complete v hv hw

#print axioms solution
