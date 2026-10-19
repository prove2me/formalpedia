-- Prove2me | solution 1 for BBCode.new336_class1_small_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:43:38.465141+00:00
-- url     : https://prove2.me/submissions/02d1cff1-aa48-41bd-a53c-00c42011840e

import Definitions.Def_BBCode_Setting
import Theorems.Thm_BBCode_new336_class1_support_left_companion163
import Theorems.Thm_BBCode_new336_class1_support_left_companion164
import Theorems.Thm_BBCode_new336_class1_support_left_companion309
import Theorems.Thm_BBCode_new336_class1_support_left_companion331
import Theorems.Thm_BBCode_new336_class1_support_left_companion335
import Theorems.Thm_BBCode_new336_class1_support_right_companion80
import Theorems.Thm_BBCode_new336_class1_support_right_companion81
import Theorems.Thm_BBCode_new336_class1_support_right_companion85
import Theorems.Thm_BBCode_new336_class1_support_right_companion226
import Theorems.Thm_BBCode_new336_class1_support_right_companion248
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

set_option maxHeartbeats 0
open Matrix BBCode BB336Cert
namespace BB336Peel
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
end BB336Peel

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

namespace BB336KernelData
open BB336Search
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

namespace BB336KernelData
lemma xnonzero : ∀ j, xmask j ≠ 0 := by decide +kernel
end BB336KernelData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BB336Cert BB336KernelData
namespace BB336Peel
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
    let w := v ∘ BB336Symmetry.shiftQ g
    have hwker : HX polyA polyB *ᵥ w = 0 := by
      have h := BB336Symmetry.kernel_reindex (HX polyA polyB)
        (BB336Symmetry.shiftG g) (BB336Symmetry.shiftQ g) v hv
      rwa [BB336Symmetry.HX_shift] at h
    have hweq : weight w = weight v := BB336Symmetry.weight_equiv _ v
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
      (BB336Symmetry.shiftG g) (BB336Symmetry.shiftQ g) v
    rw [BB336Symmetry.HZ_shift] at he
    exact he.mp hwr
end
end BB336Peel

open Matrix BBCode BB336Cert BB336KernelData BB336Search
namespace BB336Other
lemma exists_other (anchor : Fin 336) (v : Fin 336 → ZMod 2)
    (ha : v anchor ≠ 0) (hv : xH *ᵥ v = 0) :
    ∃ j ∈ xneighbors (BB336High.pick (xmask anchor)), j ≠ anchor ∧ v j ≠ 0 := by
  classical
  let T := Finset.univ.filter fun j => v j ≠ 0
  let i := BB336High.pick (xmask anchor)
  have hp : entry (xmask anchor) i = 1 := by
    simp [entry,i,BB336High.pick_spec _ (xnonzero anchor)]
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
end BB336Other

namespace BB336DistanceReduce
lemma complete (v : Qubit 2 84 → ZMod 2) (hv : HX polyA polyB *ᵥ v = 0)
    (hw : weight v ≤ 10) : v ∈ rowSpace (HZ polyA polyB) := by
  apply BB336Peel.close ?_ ?_ v hv hw
  · intro w hwker hwW haW
    have hwi : xH *ᵥ (w ∘ eqb) = 0 := by
      rw [← xtable]
      exact index_kernel _ w hwker
    have hanchor : (w ∘ eqb) 0 ≠ 0 := by
      simpa only [Function.comp_apply,show eqb (0 : Fin 336) = (Sum.inl (0,0)) from by decide +kernel] using haW
    obtain ⟨j,hj,hne,hvj⟩ := BB336Other.exists_other 0 (w ∘ eqb) hanchor hwi
    have hn : xneighbors (BB336High.pick (xmask (0 : Fin 336))) = [0, 163, 164, 309, 331, 335] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hne rfl)
    · apply BBCode.new336_class1_support_left_companion163 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (163 : Fin 336) = (Sum.inl (1,79)) from by decide +kernel] using hvj
    · apply BBCode.new336_class1_support_left_companion164 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (164 : Fin 336) = (Sum.inl (1,80)) from by decide +kernel] using hvj
    · apply BBCode.new336_class1_support_left_companion309 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (309 : Fin 336) = (Sum.inr (1,57)) from by decide +kernel] using hvj
    · apply BBCode.new336_class1_support_left_companion331 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (331 : Fin 336) = (Sum.inr (1,79)) from by decide +kernel] using hvj
    · apply BBCode.new336_class1_support_left_companion335 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (335 : Fin 336) = (Sum.inr (1,83)) from by decide +kernel] using hvj
  · intro w hwker hwW haW
    have hwi : xH *ᵥ (w ∘ eqb) = 0 := by
      rw [← xtable]
      exact index_kernel _ w hwker
    have hanchor : (w ∘ eqb) 168 ≠ 0 := by
      simpa only [Function.comp_apply,show eqb (168 : Fin 336) = (Sum.inr (0,0)) from by decide +kernel] using haW
    obtain ⟨j,hj,hne,hvj⟩ := BB336Other.exists_other 168 (w ∘ eqb) hanchor hwi
    have hn : xneighbors (BB336High.pick (xmask (168 : Fin 336))) = [80, 81, 85, 168, 226, 248] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · apply BBCode.new336_class1_support_right_companion80 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (80 : Fin 336) = (Sum.inl (0,80)) from by decide +kernel] using hvj
    · apply BBCode.new336_class1_support_right_companion81 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (81 : Fin 336) = (Sum.inl (0,81)) from by decide +kernel] using hvj
    · apply BBCode.new336_class1_support_right_companion85 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (85 : Fin 336) = (Sum.inl (1,1)) from by decide +kernel] using hvj
    · exact False.elim (hne rfl)
    · apply BBCode.new336_class1_support_right_companion226 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (226 : Fin 336) = (Sum.inr (0,58)) from by decide +kernel] using hvj
    · apply BBCode.new336_class1_support_right_companion248 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (248 : Fin 336) = (Sum.inr (0,80)) from by decide +kernel] using hvj
end BB336DistanceReduce
theorem solution (v : BBCode.Qubit 2 84 → ZMod 2)
    (hv : BBCode.HX (l := 2) (m := 84) {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10) :
    v ∈ BBCode.rowSpace (BBCode.HZ (l := 2) (m := 84)
      {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)}) := BB336DistanceReduce.complete v hv hw

#print axioms solution
