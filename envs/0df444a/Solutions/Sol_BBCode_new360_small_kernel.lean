-- Prove2me | solution 1 for BBCode.new360_small_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:37:34.887022+00:00
-- url     : https://prove2.me/submissions/787127c3-f868-45b7-a8f3-f3a7cb970f85

import Definitions.Def_BBCode_Setting
import Theorems.Thm_BBCode_new360_support_left_companion178
import Theorems.Thm_BBCode_new360_support_left_companion179
import Theorems.Thm_BBCode_new360_support_left_companion224
import Theorems.Thm_BBCode_new360_support_left_companion336
import Theorems.Thm_BBCode_new360_support_left_companion358
import Theorems.Thm_BBCode_new360_support_right_companion134
import Theorems.Thm_BBCode_new360_support_right_companion135
import Theorems.Thm_BBCode_new360_support_right_companion166
import Theorems.Thm_BBCode_new360_support_right_companion314
import Theorems.Thm_BBCode_new360_support_right_companion322
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BBNew360Cert

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

end BBNew360Cert

set_option maxHeartbeats 0
open Matrix BBCode BBNew360Cert
namespace BBNew360Bits

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
end BBNew360Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BBNew360Cert BBNew360Bits
namespace BBNew360KernelData
def xmask (j : Fin 360) : BitVec 180 := BitVec.ofNat 180 (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 383123885216472214589586756787577295904684781082771457 else 766247770432944429179173513575154591809369561091801091) else (if j.val < 3 then 1427247692705959881058285969449495136382746630 else (if j.val < 4 then 2854495385411919762116571938898990272765493260 else 5708990770823839524233143877797980545530986520))) else (if j.val < 8 then (if j.val < 6 then 11417981541647679048466287755595961091061973040 else (if j.val < 7 then 22835963083295358096932575511191922182123946080 else 45671926166590716193865151022383844364247892160)) else (if j.val < 9 then 91343852333181432387730302044767688728495784320 else (if j.val < 10 then 182687704666362864775460604089535377456991568640 else 365375409332725729550921208179070754913983137280)))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then 730750818665451459101842416358141509827966274560 else 1461501637330902918203684832716283019655932549120) else (if j.val < 14 then 2923003274661805836407369665432566039311865098240 else (if j.val < 15 then 5846006549323611672814739330865132078623730196480 else 11692013098647223345629478661730264157247460392960))) else (if j.val < 19 then (if j.val < 17 then 23384026197294446691258957323460528314494920785920 else (if j.val < 18 then 46768052394588893382517914646921056628989841571840 else 93536104789177786765035829293842113257979683143680)) else (if j.val < 20 then 187072209578355573530071658587684226515959366287360 else (if j.val < 21 then 374144419156711147060143317175368453031918732574720 else 748288838313422294120286634350736906063837465149440))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then 1496577676626844588240573268701473812127674930298880 else 2993155353253689176481146537402947624255349860597760) else (if j.val < 25 then 5986310706507378352962293074805895248510699721195520 else (if j.val < 26 then 11972621413014756705924586149611790497021399442391040 else 23945242826029513411849172299223580994042798884782080))) else (if j.val < 30 then (if j.val < 28 then 47890485652059026823698344598447161988085597769564160 else (if j.val < 29 then 95780971304118053647396689196894323976171195539128320 else 191561942608236107294793378393788647952342391078256640)) else (if j.val < 31 then 576460753645600768 else (if j.val < 32 then 3758096384 else 6442450945)))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then 12884901890 else (if j.val < 35 then 25769803780 else 51539607560)) else (if j.val < 37 then 103079215120 else (if j.val < 38 then 206158430240 else 412316860480))) else (if j.val < 42 then (if j.val < 40 then 824633720960 else (if j.val < 41 then 1649267441920 else 3298534883840)) else (if j.val < 43 then 6597069767680 else (if j.val < 44 then 13194139535360 else 26388279070720)))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then 52776558141440 else 105553116282880) else (if j.val < 48 then 211106232565760 else (if j.val < 49 then 422212465131520 else 844424930263040))) else (if j.val < 53 then (if j.val < 51 then 1688849860526080 else (if j.val < 52 then 3377699721052160 else 6755399442104320)) else (if j.val < 54 then 13510798884208640 else (if j.val < 55 then 27021597768417280 else 54043195536834560)))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then 108086391073669120 else 216172782147338240) else (if j.val < 59 then 432345564294676480 else (if j.val < 60 then 864691128589352960 else 618970021083842018208120832))) else (if j.val < 64 then (if j.val < 62 then 4035225266123964416 else (if j.val < 63 then 6917529028714823680 else 13835058057429647360)) else (if j.val < 65 then 27670116114859294720 else (if j.val < 66 then 55340232229718589440 else 110680464459437178880))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then 221360928918874357760 else 442721857837748715520) else (if j.val < 70 then 885443715675497431040 else (if j.val < 71 then 1770887431350994862080 else 3541774862701989724160))) else (if j.val < 75 then (if j.val < 73 then 7083549725403979448320 else (if j.val < 74 then 14167099450807958896640 else 28334198901615917793280)) else (if j.val < 76 then 56668397803231835586560 else (if j.val < 77 then 113336795606463671173120 else 226673591212927342346240)))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then 453347182425854684692480 else (if j.val < 80 then 906694364851709369384960 else 1813388729703418738769920)) else (if j.val < 82 then 3626777459406837477539840 else (if j.val < 83 then 7253554918813674955079680 else 14507109837627349910159360))) else (if j.val < 87 then (if j.val < 85 then 29014219675254699820318720 else (if j.val < 86 then 58028439350509399640637440 else 116056878701018799281274880)) else (if j.val < 88 then 232113757402037598562549760 else (if j.val < 89 then 464227514804075197125099520 else 928455029608150394250199040))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then 664613999439882985558628873764077568 else 4332790137498830962146934784) else (if j.val < 93 then 7427640236865203154001592320 else (if j.val < 94 then 14855280473730406308003184640 else 29710560947460812616006369280))) else (if j.val < 98 then (if j.val < 96 then 59421121894921625232012738560 else (if j.val < 97 then 118842243789843250464025477120 else 237684487579686500928050954240)) else (if j.val < 99 then 475368975159373001856101908480 else (if j.val < 100 then 950737950318746003712203816960 else 1901475900637492007424407633920)))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then 3802951801274984014848815267840 else 7605903602549968029697630535680) else (if j.val < 104 then 15211807205099936059395261071360 else (if j.val < 105 then 30423614410199872118790522142720 else 60847228820399744237581044285440))) else (if j.val < 109 then (if j.val < 107 then 121694457640799488475162088570880 else (if j.val < 108 then 243388915281598976950324177141760 else 486777830563197953900648354283520)) else (if j.val < 110 then 973555661126395907801296708567040 else (if j.val < 111 then 1947111322252791815602593417134080 else 3894222644505583631205186834268160))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then 7788445289011167262410373668536320 else 15576890578022334524820747337072640) else (if j.val < 115 then 31153781156044669049641494674145280 else (if j.val < 116 then 62307562312089338099282989348290560 else 124615124624178676198565978696581120))) else (if j.val < 120 then (if j.val < 118 then 249230249248357352397131957393162240 else (if j.val < 119 then 498460498496714704794263914786324480 else 996920996993429409588527829572648960)) else (if j.val < 121 then 713623848014514935260287825854506393541804032 else (if j.val < 122 then 4652297985247205555163324710981206016 else 7975367975947435276708222636581191680)))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then 15950735951894870553416445273162383360 else (if j.val < 125 then 31901471903789741106832890546324766720 else 63802943807579482213665781092649533440)) else (if j.val < 127 then 127605887615158964427331562185299066880 else (if j.val < 128 then 255211775230317928854663124370598133760 else 510423550460635857709326248741196267520))) else (if j.val < 132 then (if j.val < 130 then 1020847100921271715418652497482392535040 else (if j.val < 131 then 2041694201842543430837304994964785070080 else 4083388403685086861674609989929570140160)) else (if j.val < 133 then 8166776807370173723349219979859140280320 else (if j.val < 134 then 16333553614740347446698439959718280560640 else 32667107229480694893396879919436561121280)))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then 65334214458961389786793759838873122242560 else 130668428917922779573587519677746244485120) else (if j.val < 138 then 261336857835845559147175039355492488970240 else (if j.val < 139 then 522673715671691118294350078710984977940480 else 1045347431343382236588700157421969955880960))) else (if j.val < 143 then (if j.val < 141 then 2090694862686764473177400314843939911761920 else (if j.val < 142 then 4181389725373528946354800629687879823523840 else 8362779450747057892709601259375759647047680)) else (if j.val < 144 then 16725558901494115785419202518751519294095360 else (if j.val < 145 then 33451117802988231570838405037503038588190720 else 66902235605976463141676810075006077176381440)))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then 133804471211952926283353620150012154352762880 else 267608942423905852566707240300024308705525760) else (if j.val < 149 then 535217884847811705133414480600048617411051520 else (if j.val < 150 then 1070435769695623410266828961200097234822103040 else 766247772217004045061623364898012053621238481570234368))) else (if j.val < 154 then (if j.val < 152 then 4995366924470859583704000893073232977339613184 else (if j.val < 153 then 8563486157564987282134631689600777878576824320 else 17126972315129974564269263379201555757153648640)) else (if j.val < 155 then 34253944630259949128538526758403111514307297280 else (if j.val < 156 then 68507889260519898257077053516806223028614594560 else 137015778521039796514154107033612446057229189120))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 274031557042079593028308214067224892114458378240 else 548063114084159186056616428134449784228916756480) else (if j.val < 160 then 1096126228168318372113232856268899568457833512960 else (if j.val < 161 then 2192252456336636744226465712537799136915667025920 else 4384504912673273488452931425075598273831334051840))) else (if j.val < 165 then (if j.val < 163 then 8769009825346546976905862850151196547662668103680 else (if j.val < 164 then 17538019650693093953811725700302393095325336207360 else 35076039301386187907623451400604786190650672414720)) else (if j.val < 166 then 70152078602772375815246902801209572381301344829440 else (if j.val < 167 then 140304157205544751630493805602419144762602689658880 else 280608314411089503260987611204838289525205379317760)))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then 561216628822179006521975222409676579050410758635520 else (if j.val < 170 then 1122433257644358013043950444819353158100821517271040 else 2244866515288716026087900889638706316201643034542080)) else (if j.val < 172 then 4489733030577432052175801779277412632403286069084160 else (if j.val < 173 then 8979466061154864104351603558554825264806572138168320 else 17958932122309728208703207117109650529613144276336640))) else (if j.val < 177 then (if j.val < 175 then 35917864244619456417406414234219301059226288552673280 else (if j.val < 176 then 71835728489238912834812828468438602118452577105346560 else 143671456978477825669625656936877204236905154210693120)) else (if j.val < 178 then 287342913956955651339251313873754408473810308421386240 else (if j.val < 179 then 574685827913911302678502627747508816947620616842772480 else 1149371655827822605357005255495017633895241233685544960)))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then 21778071482940061661655974875633169727489 else 43556142965880123323311949751266339454978) else (if j.val < 183 then 87112285931760246646623899502532678909956 else (if j.val < 184 then 174224571863520493293247799005065357819912 else 348449143727040986586495598010130715639824))) else (if j.val < 188 then (if j.val < 186 then 696898287454081973172991196020261431279648 else (if j.val < 187 then 1393796574908163946345982392040522862559296 else 2787593149816327892691964784081045725118592)) else (if j.val < 189 then 5575186299632655785383929568162090376495361 else (if j.val < 190 then 11150372599265311570767859136324180752990722 else 22300745198530623141535718272648361505981444)))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then 44601490397061246283071436545296723011962888 else 89202980794122492566142873090593446023925776) else (if j.val < 194 then 178405961588244985132285746181186892047851552 else (if j.val < 195 then 356811923176489970264571492362373784095703104 else 713623846352979940529142984724747568191406208))) else (if j.val < 199 then (if j.val < 197 then 1329227995784915872903807060280410368 else (if j.val < 198 then 2658455991569831745807614120560820736 else 5316911983139663491615228241121641472)) else (if j.val < 200 then 10633823966279326983230456482243282944 else (if j.val < 201 then 21267647932558653966460912964486565888 else 42535295865117307932921825928973131776))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then 85070591730234615865843651857946263552 else 170141183460469231731687303715892527104) else (if j.val < 205 then 340282366920938463463374607431785054208 else (if j.val < 206 then 680564733841876926926749214863570108416 else 1361129467683753853853498429727140216832))) else (if j.val < 210 then (if j.val < 208 then 2722258935367507707706996859454280433664 else (if j.val < 209 then 5444517870735015415413993718908560867328 else 10889035741470030830827987437817121734656)) else (if j.val < 211 then 23384026197294446691258957323460532818095621799936 else (if j.val < 212 then 46768052394588893382517914646921065636191243599872 else 93536104789177786765035829293842131272382487199744)))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then 187072209578355573530071658587684262544764974399488 else (if j.val < 215 then 374144419156711147060143317175368525089529948798976 else 748288838313422294120286634350737050179059897597952)) else (if j.val < 217 then 1496577676626844588240573268701474100358119795195904 else (if j.val < 218 then 2993155353253689176481146537402948200716239590391808 else 5986310706507378352962293074805895248510975647678464))) else (if j.val < 222 then (if j.val < 220 then 11972621413014756705924586149611790497021951295356928 else (if j.val < 221 then 23945242826029513411849172299223580994043902590713856 else 47890485652059026823698344598447161988087805181427712)) else (if j.val < 223 then 95780971304118053647396689196894323976175610362855424 else (if j.val < 224 then 191561942608236107294793378393788647952351220725710848 else 383123885216472214589586756787577295904702441451421696)))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then 766247770432944429179173513575154591809404882902843392 else 1427247692705959881058285969449565780004831232) else (if j.val < 228 then 2854495385411919762116571938899131560009662464 else (if j.val < 229 then 5708990770823839524233143877798263120019324928 else 11417981541647679048466287755596526240038649856))) else (if j.val < 233 then (if j.val < 231 then 22835963083295358096932575511193052480077299712 else (if j.val < 232 then 45671926166590716193865151022386104960154599424 else 91343852333181432387730302044772209920309198848)) else (if j.val < 234 then 182687704666362864775460604089544419840618397696 else (if j.val < 235 then 365375409332725729550921208179088839681236795392 else 730750818665451459101842416358177679362473590784)))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then 1461501637330902918203684832716355358724947181568 else 2923003274661805836407369665432710717449894363136) else (if j.val < 239 then 5846006549323611672814739330865421434899788726272 else (if j.val < 240 then 11692013098647223345629478661730842869799577452544 else 4835704431380021305688064))) else (if j.val < 244 then (if j.val < 242 then 9671408862760042611376128 else (if j.val < 243 then 19342817725520085222752256 else 38685635451040170445504512)) else (if j.val < 245 then 77371270902080340891009024 else (if j.val < 246 then 154742541804160681782018048 else 309485083608321363564036096))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then 618970167216642727128072192 else 296300826683963867136) else (if j.val < 250 then 592601653367927734272 else (if j.val < 251 then 1185203306735855468544 else 2370406613471710937088))) else (if j.val < 255 then (if j.val < 253 then 4740813226943421874176 else (if j.val < 254 then 9481626453886843748352 else 18963252907773687496704)) else (if j.val < 256 then 37926505815547374993408 else (if j.val < 257 then 75853011631093676244993 else 151706023262187352489986)))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then 303412046524374704979972 else (if j.val < 260 then 606824093048749409959944 else 1213648186097498819919888)) else (if j.val < 262 then 2427296372194997639839776 else (if j.val < 263 then 4854592744389995279679552 else 9709185488779990559359104))) else (if j.val < 267 then (if j.val < 265 then 19418370977559981118718208 else (if j.val < 266 then 38836741955119962237436416 else 77673483910239924474872832)) else (if j.val < 268 then 155346967820479848949745664 else (if j.val < 269 then 310693935640959697899491328 else 621387871281919395798982656))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then 5192298096474866913928363414388736 else 10384596192949733827856726828777472) else (if j.val < 273 then 20769192385899467655713453657554944 else (if j.val < 274 then 41538384771798935311426907315109888 else 83076769543597870622853814630219776))) else (if j.val < 278 then (if j.val < 276 then 166153539087195741245707629260439552 else (if j.val < 277 then 332307078174391482491415258520879104 else 664614156348782964982830517041758208)) else (if j.val < 279 then 318150590096347234248702296064 else (if j.val < 280 then 636301180192694468497404592128 else 1272602360385388936994809184256)))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then 2545204720770777873989618368512 else 5090409441541555747979236737024) else (if j.val < 284 then 10180818883083111495958473474048 else (if j.val < 285 then 20361637766166222991916946948096 else 40723275532332445983833893896192))) else (if j.val < 289 then (if j.val < 287 then 81446551064663739046164254687232 else (if j.val < 288 then 162893102129327478092328509374464 else 325786204258654956184657018748928)) else (if j.val < 290 then 651572408517309912369314037497856 else (if j.val < 291 then 1303144817034619824738628074995712 else 2606289634069239649477256149991424))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then 5212579268138479298954512299982848 else 10425158536276958597909024599965696) else (if j.val < 295 then 20850317072553917195818049199931392 else (if j.val < 296 then 41700634145107834391636098399862784 else 83401268290215668783272196799725568))) else (if j.val < 300 then (if j.val < 298 then 166802536580431337566544393599451136 else (if j.val < 299 then 333605073160862675133088787198902272 else 667210146321725350266177574397804544)) else (if j.val < 301 then 5575187628860651570318691937900629237694464 else (if j.val < 302 then 11150375257721303140637383875801258475388928 else 22300750515442606281274767751602516950777856)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then 44601501030885212562549535503205033901555712 else (if j.val < 305 then 89203002061770425125099071006410067803111424 else 178406004123540850250198142012820135606222848)) else (if j.val < 307 then 356812008247081700500396284025640271212445696 else (if j.val < 308 then 713624016494163401000792568051280542424891392 else 341611594916728215039556873008747380736))) else (if j.val < 312 then (if j.val < 310 then 683223189833456430079113746017494761472 else (if j.val < 311 then 1366446379666912860158227492034989522944 else 2732892759333825720316454984069979045888)) else (if j.val < 313 then 5465785518667651440632909968139958091776 else (if j.val < 314 then 10931571037335302881265819936279916183552 else 21863142074670605762531639872559832367104)))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 43726284149341211525063279745119664734208 else 87452568298681185110088427031469037191168) else (if j.val < 318 then 174905136597362370220176854062938074382336 else (if j.val < 319 then 349810273194724740440353708125876148764672 else 699620546389449480880707416251752297529344))) else (if j.val < 323 then (if j.val < 321 then 1399241092778898961761414832503504595058688 else (if j.val < 322 then 2798482185557797923522829665007009190117376 else 5596964371115595847045659330014018380234752)) else (if j.val < 324 then 11193928742231191694091318660028036760469504 else (if j.val < 325 then 22387857484462383388182637320056073520939008 else 44775714968924766776365274640112147041878016)))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then 89551429937849533552730549280224294083756032 else 179102859875699067105461098560448588167512064) else (if j.val < 329 then 358205719751398134210922197120897176335024128 else (if j.val < 330 then 716411439502796268421844394241794352670048256 else 5986312133755071058942456542695516368429783330062336))) else (if j.val < 334 then (if j.val < 332 then 11972624267510142117884913085391032736859566660124672 else (if j.val < 333 then 23945248535020284235769826170782065473719133320249344 else 47890497070040568471539652341564130947438266640498688)) else (if j.val < 335 then 95780994140081136943079304683128261894876533280997376 else (if j.val < 336 then 191561988280162273886158609366256523789753066561994752 else 383123976560324547772317218732513047579506133123989504))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then 766247953120649095544634437465026095159012266247979008 else 366802657025436881728838028976148780546695102464) else (if j.val < 340 then 733605314050873763457676057952297561093390204928 else (if j.val < 341 then 1467210628101747526915352115904595122186780409856 else 2934421256203495053830704231809190244373560819712))) else (if j.val < 345 then (if j.val < 343 then 5868842512406990107661408463618380488747121639424 else (if j.val < 344 then 11737685024813980215322816927236760977494243278848 else 23475370049627960430645633854473521954988486557696)) else (if j.val < 346 then 46950740099255920861291267708947043909976973115392 else (if j.val < 347 then 93901480198510512494587988442060469393168565010432 else 187802960397021024989175976884120938786337130020864)))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then 375605920794042049978351953768241877572674260041728 else (if j.val < 350 then 751211841588084099956703907536483755145348520083456 else 1502423683176168199913407815072967510290697040166912)) else (if j.val < 352 then 3004847366352336399826815630145935020581394080333824 else (if j.val < 353 then 6009694732704672799653631260291870041162788160667648 else 12019389465409345599307262520583740082325576321335296))) else (if j.val < 357 then (if j.val < 355 then 24038778930818691198614525041167480164651152642670592 else (if j.val < 356 then 48077557861637382397229050082334960329302305285341184 else 96155115723274764794458100164669920658604610570682368)) else (if j.val < 358 then 192310231446549529588916200329339841317209221141364736 else (if j.val < 359 then 384620462893099059177832400658679682634418442282729472 else 769240925786198118355664801317359365268836884565458944)))))))))
def xrow (i : Fin 180) : BitVec 360 := BitVec.ofNat 360 (if i.val < 90 then (if i.val < 45 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 115792089237316195423964836362690441289868079851618193499647599962318610366467 else 231584178474632390847929672725380882579736159703236386999295199924637220732934) else (if i.val < 3 then 463168356949264781695859345450761765159472319406472773998590399849274441465868 else (if i.val < 4 then 926336713898529563391718690901523530318944638812945547997180799698548882931736 else 1852673427797059126783437381803047060637889277625891095994361599397097765863472))) else (if i.val < 8 then (if i.val < 6 then 3705346855594118253566874763606094121275778555251782191988723198794195531726944 else (if i.val < 7 then 7410693711188236507133749527212188242551557110503564383977446397588391063453888 else 14821387422376473014267499054424376485103114221007128767954892795176782126907776)) else (if i.val < 9 then 29642774844752946028534998108848752970206228442014257535909785590353564253815552 else (if i.val < 10 then 59285549689505892057069996217697505940412456884028515071819571180707128507631104 else 118571099379011784114139992435395011880824913768057030143639142361414257015262208)))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then 237142198758023568228279984870790023761649827536114060287278284722828514030524416 else 474284397516047136456559969741580047523299655072228120574556569445657028061048832) else (if i.val < 14 then 948568795032094272913119939483160095046599310144456241149113138891314056122097664 else (if i.val < 15 then 1766847064784837190167275008568141707354541377951372179518585597516103680 else 3533694129569674380334550017136283414709082755902744359037171195032207360))) else (if i.val < 19 then (if i.val < 17 then 7067388259139348760669100034272566829418165511805488718074342390064414720 else (if i.val < 18 then 14134776518278697521338200068545133658836331023610977436148684780128829440 else 28269553036557395042676400137090267317672662047221954872297369560257658880)) else (if i.val < 20 then 56539106073114790085352800274180534635345324094443909744594739120515317760 else (if i.val < 21 then 113078212146229580170705600548361069270690648188887819489189478241030635520 else 226156424292459160341411201096722138541381296377775638978378956482061271040))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then 452312848583272816127033691692155196758563589277718851274743072222957535232 else 904625697166545632254067383384310393517127178555437702549486144445915070464) else (if i.val < 25 then 1809251394333091264508134766768620787034254357110875405098972288891830140928 else (if i.val < 26 then 3618502788666182529016269533537241574068508714221750810197944577783660281856 else 7237005577332365058032539067074483148137017428443501620395889155567320563712))) else (if i.val < 30 then (if i.val < 28 then 14474011154664730116065078134148966296274034856887003240791778311134641127424 else (if i.val < 29 then 28948022309329460232130156268297932592548069713774006481582403700765749149696 else 57896044618658920464260312536595865185096139427548012963164807401530424557569)) else (if i.val < 31 then 124330809102446660539268456707936759977947864779254168439896557340762315964035585015808 else (if i.val < 32 then 248661618204893321078536913415873519955895729558508336879793114681524631928071170031616 else 497323236409786642157073826831747039911791459117016673759586229363049263856142340063232)))) else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then 994646472819573284314147653663494079823582918234033347519172458726098527712284680126464 else (if i.val < 35 then 1989292945639146568628295307326988159647165836468066695038344917452197055424569360252928 else 3978585891278293137256590614653976319294331672936133390076689834904394110849138720505856)) else (if i.val < 37 then 7957171782556586274513181229307952638588663345872266780153379669808788221698277441011712 else (if i.val < 38 then 15914343565113172549026362458615905277177326691744533560306759339617576443396554882023424 else 31828687130226345098052724917231810554354653383489067120613518679235152886793109764046848))) else (if i.val < 42 then (if i.val < 40 then 63657374260452690196105449834463621108709306766978134241227037358470305773586219528093696 else (if i.val < 41 then 127314748520905380392210899668927242217418613533956268482454074716940611547172439056187392 else 254629497041810760784421799337854484434837227067912536964908149433881223094344878112374784)) else (if i.val < 43 then 509258994083621521568843598675708968869674454135825073929816298867762446188689756224749568 else (if i.val < 44 then 1018517988167243043137687197351417937739348908271650147859632597735524892377379512449499136 else 1897137590071117252113244732809572105145339473844979747339141541377071034736312320)))))) else (if i.val < 67 then (if i.val < 56 then (if i.val < 50 then (if i.val < 47 then (if i.val < 46 then 3794275180142234504226489465619144210290678947689959494678283082754142069472624640 else 7588550360284469008452978931238288420581357895379918989356566165508284138945249280) else (if i.val < 48 then 15177100720568938016905957862476576841162715790759837978713132331016568277890498560 else (if i.val < 49 then 30354201441137876033811915724953153682325431581519675957426264662033136555780997120 else 60708402882275752067623831449906307364650863163039351914852529324066273111561994240))) else (if i.val < 53 then (if i.val < 51 then 121416805764551504135247662899812614729301726326078703829705058648132546223123988480 else (if i.val < 52 then 242833611529103008270495325799625229458603452652157407659410117296265092446247976960 else 485667223056439169477857771826988367458618955971044681926927351500042158554551943168)) else (if i.val < 54 then 971334446112878338955715543653976734917237911942089363853854703000084317109103886336 else (if i.val < 55 then 1942668892225756677911431087307953469834475823884178727707709406000168634218207772672 else 3885337784451513355822862174615906939668951647768357455415418812000337268436415545344)))) else (if i.val < 61 then (if i.val < 58 then (if i.val < 57 then 7770675568903026711645724349231813879337903295536714910830837624000674536872831090688 else 15541351137806053423291448698463627758675806591073429821661675248001349073745662181376) else (if i.val < 59 then 31082702275612106846582897396927255517351613182146859643322112555964565688721032085504 else (if i.val < 60 then 62165404551224213693165794793854511034703226364293719286644225111927978455938531065856 else 133499189745056880150142936331245051935371940104981728180257763850390718693687887455780750753792))) else (if i.val < 64 then (if i.val < 62 then 266998379490113760300285872662490103870743880209963456360515527700781437387375774911561501507584 else (if i.val < 63 then 533996758980227520600571745324980207741487760419926912721031055401562874774751549823123003015168 else 1067993517960455041201143490649960415482975520839853825442062110803125749549503099646246006030336)) else (if i.val < 65 then 2135987035920910082402286981299920830965951041679707650884124221606251499099006199292492012060672 else (if i.val < 66 then 4271974071841820164804573962599841661931902083359415301768248443212502998198012398584984024121344 else 8543948143683640329609147925199683323863804166718830603536496886425005996396024797169968048242688))))) else (if i.val < 78 then (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then 17087896287367280659218295850399366647727608333437661207072993772850011992792049594339936096485376 else 34175792574734561318436591700798733295455216666875322414145987545700023985584099188679872192970752) else (if i.val < 70 then 68351585149469122636873183401597466590910433333750644828291975091400047971168198377359744385941504 else (if i.val < 71 then 136703170298938245273746366803194933181820866667501289656583950182800095942336396754719488771883008 else 273406340597876490547492733606389866363641733335002579313167900365600191884672793509438977543766016))) else (if i.val < 75 then (if i.val < 73 then 546812681195752981094985467212779732727283466670005158626335800731200383769345587018877955087532032 else (if i.val < 74 then 1093625362391505962189970934425559465454566933340010317252671601462400767538691174037755910175064064 else 2037035976341925728001943253965342596838276591745508847150988985232387724615335349510471680)) else (if i.val < 76 then 4074071952683851456003886507930685193676553183491017694301977970464775449230670699020943360 else (if i.val < 77 then 8148143905367702912007773015861370387353106366982035388603955940929550898461341398041886720 else 16296287810735405824015546031722740774706212733964070777207911881859101796922682796083773440)))) else (if i.val < 84 then (if i.val < 81 then (if i.val < 79 then 32592575621470811648031092063445481549412425467928141554415823763718203593845365592167546880 else (if i.val < 80 then 65185151242941623296062184126890963098824850935856283108831647527436407187690731184335093760 else 130370302485883246592124368253781926197649701871712566217663295054872814375381462368670187520)) else (if i.val < 82 then 260740604971766493184248736507563852395299403743425132435326590109745628750762924737340375040 else (if i.val < 83 then 521481209941635848780200131534086302101799762305325207957718809115144403403261806959952658432 else 1042962419883271697560400263068172604203599524610650415915437618230288806806523613919905316864))) else (if i.val < 87 then (if i.val < 85 then 2085924839766543395120800526136345208407199049221300831830875236460577613613047227839810633728 else (if i.val < 86 then 4171849679533086790241601052272690416814398098442601663661750472921155227226094455679621267456 else 8343699359066173580483202104545380833628796196885203327323500945842310454452188911359242534912)) else (if i.val < 88 then 16687398718132347160966404209090761667257592393770406654647001891684620908904377822718485069824 else (if i.val < 89 then 33374797436264694321932808418181523334515184787540813309292674555374694841975137218651588919296 else 66749594872529388643865616836363046669030369575081626618585349110748151743912141978532885561344))))))) else (if i.val < 135 then (if i.val < 112 then (if i.val < 101 then (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then 143343663499379469476163870317026930256060997086741832302942172146879793402831329563476742658465996996608 else 286687326998758938952327740634053860512121994173483664605884344293759586805662659126953485316931993993216) else (if i.val < 93 then 573374653997517877904655481268107721024243988346967329211768688587519173611325318253906970633863987986432 else (if i.val < 94 then 1146749307995035755809310962536215442048487976693934658423537377175038347222650636507813941267727975972864 else 2293498615990071511618621925072430884096975953387869316847074754350076694445301273015627882535455951945728))) else (if i.val < 98 then (if i.val < 96 then 4586997231980143023237243850144861768193951906775738633694149508700153388890602546031255765070911903891456 else (if i.val < 97 then 9173994463960286046474487700289723536387903813551477267388299017400306777781205092062511530141823807782912 else 18347988927920572092948975400579447072775807627102954534776598034800613555562410184125023060283647615565824)) else (if i.val < 99 then 36695977855841144185897950801158894145551615254205909069553196069601227111124820368250046120567295231131648 else (if i.val < 100 then 73391955711682288371795901602317788291103230508411818139106392139202454222249640736500092241134590462263296 else 146783911423364576743591803204635576582206461016823636278212784278404908444499281473000184482269180924526592)))) else (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 293567822846729153487183606409271153164412922033647272556425568556809816888998562946000368964538361849053184 else 587135645693458306974367212818542306328825844067294545112851137113619633777997125892000737929076723698106368) else (if i.val < 104 then 1174271291386916613948734425637084612657651688134589090225702274227239267555994251784001475858153447396212736 else (if i.val < 105 then 2187250724791000178857334425057242192714027740637326013348040116407333059303679876555051368783544320 else 4374501449582000357714668850114484385428055481274652026696080232814666118607359753110102737567088640))) else (if i.val < 109 then (if i.val < 107 then 8749002899164000715429337700228968770856110962549304053392160465629332237214719506220205475134177280 else (if i.val < 108 then 17498005798328001430858675400457937541712221925098608106784320931258664474429439012440410950268354560 else 34996011596656002861717350800915875083424443850197216213568641862517328948858878024880821900536709120)) else (if i.val < 110 then 69992023193312005723434701601831750166848887700394432427137283725034657897717756049761643801073418240 else (if i.val < 111 then 139984046386624011446869403203663500333697775400788864854274567450069315795435512099523287602146836480 else 279968092773248022893738806407327000667395550801577729708549134900138631590871024199046575204293672960))))) else (if i.val < 123 then (if i.val < 117 then (if i.val < 114 then (if i.val < 113 then 559936185544459009813040264318449744192201510460486333705700308978402977733610140154715462418424659968 else 1119872371088918019626080528636899488384403020920972667411400617956805955467220280309430924836849319936) else (if i.val < 115 then 2239744742177836039252161057273798976768806041841945334822801235913611910934440560618861849673698639872 else (if i.val < 116 then 4479489484355672078504322114547597953537612083683890669645602471827223821868881121237723699347397279744 else 8958978968711344157008644229095195907075224167367781339291204943654447643737762242475447398694794559488))) else (if i.val < 120 then (if i.val < 118 then 17917957937422688314017288458190391814150448334735562678582409887308895287475524484950894797389589118976 else (if i.val < 119 then 35835915874845376628034576916380783628300896669471125357163392526926413843065775599805243906703075835904 else 71671831749690753256069153832761567256601793338942250714326785053851498458137004223776869386620770451456)) else (if i.val < 121 then 523518245917962924170990541921210287823855143364746828560930390318326543173374046640057352192 else (if i.val < 122 then 1047036491835925848341981083842420575647710286729493657121860780636653086346748093280114704384 else 2094072983671851696683962167684841151295420573458987314243721561273306172693496186560229408768)))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 124 then 4188145967343703393367924335369682302590841146917974628487443122546612345386992373120458817536 else (if i.val < 125 then 8376291934687406786735848670739364605181682293835949256974886245093224690773984746240917635072 else 16752583869374813573471697341478729210363364587671898513949772490186449381547969492481835270144)) else (if i.val < 127 then 33505167738749627146943394682957458420726729175343797027899544980372898763095938984963670540288 else (if i.val < 128 then 67010335477499254293886789365914916841453458350687594055799089960745797526191877969927341080576 else 134020670954998508587773578731829833682906916701375188111598179921491595052383755939854682161152))) else (if i.val < 132 then (if i.val < 130 then 268041341909997017175547157463659667365813833402750376223196359842983190104767511879709364322304 else (if i.val < 131 then 536082683819994034351094314927319334731627666805500752446392719685966380209535023759418728644608 else 1072165367639988068702188629854638669463255333611001504892785439371932760419070047518837457289216)) else (if i.val < 133 then 2144330735279976137404377259709277338926510667222003009785570878743865520838140095037674914578432 else (if i.val < 134 then 4288661470559952274808754519418554677853021334444006019571141757487731041676280190075349829156864 else 8577322941119904549617509038837107710201486880177510750061959315971984250925878365309958493306880)))))) else (if i.val < 157 then (if i.val < 146 then (if i.val < 140 then (if i.val < 137 then (if i.val < 136 then 17154645882239809099235018077674215420402973760355021500123918631943968501851756730619916986613760 else 34309291764479618198470036155348430840805947520710043000247837263887937003703513461239833973227520) else (if i.val < 138 then 68618583528959236396940072310696861681611895041420086000495674527775874007407026922479667946455040 else (if i.val < 139 then 137237167057918472793880144621393723363223790082840172000991349055551748014814053844959335892910080 else 274474334115836945587760289242787446726447580165680344001982698111103496029628107689918671785820160))) else (if i.val < 143 then (if i.val < 141 then 548948668231673891175520578485574893452895160331360688003965396222206992059256215379837343571640320 else (if i.val < 142 then 1097897336463347782351041156971149786905790320662721376007930792444413984118512430759674687143280640 else 8543950180719616664066173093123896867789371483698709256027229115015418392030238059172903446904832)) else (if i.val < 144 then 17087900361439233328132346186247793735578742967397418512054458230030836784060476118345806893809664 else (if i.val < 145 then 34175800722878466656264692372495587471157485934794837024108916460061673568120952236691613787619328 else 68351601445756933312529384744991174942314971869589674048217832920123347136241904473383227575238656)))) else (if i.val < 151 then (if i.val < 148 then (if i.val < 147 then 136703202891513866625058769489982349884629943739179348096435665840246694272483808946766455150477312 else 273406405783027733250117538979964699769259887478358696192871331680493388544967617893532910300954624) else (if i.val < 149 then 546812811566055466500235077959929399538519773424221852947101497708599630997912021617821834801053696 else (if i.val < 150 then 1093625623132110933000470155919858799077039546848443704466955304040467376722453946689955593499705344 else 562123436269234064563733072369228798735551212342114774833765137003998494985992160339081296318514069508))) else (if i.val < 154 then (if i.val < 152 then 1124246872538468129127466144738457597471102424684229549667530274007996989971984320678162592637028139016 else (if i.val < 153 then 2248493745076936258254932289476915194942204849368459099335060548015993979943968641356325185274056278032 else 4496987490153872516509864578953830389884409698736918198670121096031987959887937282712650370548112556064)) else (if i.val < 155 then 8993974980307745033019729157907660779768819397473836397340242192063975919775874565425300741096225112128 else (if i.val < 156 then 17987949960615490066039458315815321559537638794947672794680484384127951839551749130850601482192450224256 else 35975899921230980132078916631630643119075277589895345589360968768255903679103498261701202964384900448512))))) else (if i.val < 168 then (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then 71951799842461960264157833263261286238150555179790691178721937536511807358206996523402405928769800897024 else 143903599684923920528315666526522572476301110359581382357443875073023614716413993046804811857539601794048) else (if i.val < 160 then 287807199369847841056631333053045144952602220719162764714887750146047229432827986093609623715079203588096 else (if i.val < 161 then 575614398739695682113262666106090289905204441438325529429775500292094458865655972187219247430158407176192 else 1151228797479391364226525332212180579810408882876651058859551000584188917731311944374438494860316814352384))) else (if i.val < 165 then (if i.val < 163 then 2302457594958782728453050664424361159620817765753302117719102001168377835462623888748876989720633628704768 else (if i.val < 164 then 4604915189917565456906101328848722319241635531506604235438204002336755670925247777497753979441267257409536 else 9209830379835130913812202657697442871636207930133436208784949416724178071717103662112415470856196570808320)) else (if i.val < 166 then 18419660759670261827624405315394885743272415860266872417569898833448356143434207324224830941712393141616640 else (if i.val < 167 then 36839321519340523655248810630789771486544831720533744835139797666896712286868414648449661883424786283233280 else 73678643038681047310497621261579542973089663441067489670279595333793424573736829296899323766849572566466560)))) else (if i.val < 174 then (if i.val < 171 then (if i.val < 169 then 147357286077362094620995242523159085946179326882134979340559190667586849147473658593798647533699145132933120 else (if i.val < 170 then 294714572154724189241990485046318171892358653764269958681118381335173698294947317187597295067398290265866240 else 589429144309448378483980970092636343784717307528539917362236762670347396589894634375194590134796580531732480)) else (if i.val < 172 then 1178858288618896756967961940185272687569434615057079834724473525340694793179789268750389180269593161063464960 else (if i.val < 173 then 9173996651211010829455207953710574880808046559009229634868515574951167654923093236455285377930796118048768 else 18347993302422021658910415907421149761616093118018459269737031149902335309846186472910570755861592236097536))) else (if i.val < 177 then (if i.val < 175 then 36695986604844043317820831814842299523232186236036918539474062299804670619692372945821141511723184472195072 else (if i.val < 176 then 73391973209688086635641663629684599046464372472073837078948124599609341239384745891642283023446368944390144 else 146783946419376173271283327259369198092928744944147674157896249199218682478769491783284566046892737888780288)) else (if i.val < 178 then 293567892838752346542566654518738396185857489888295348315792498398437364957538983566569132093785475777560576 else (if i.val < 179 then 587135785677504693085133309037476792371714979776590696631584996796874729915077967133138264187570950481379329 else 1174271571355009386170266618074953584743429959553181391730674454155108294177768788174253314205897915161903106))))))))
def xH : Matrix (Fin 180) (Fin 360) (ZMod 2) := fun i j => entry (xmask j) i
def zmask (j : Fin 360) : BitVec 180 := BitVec.ofNat 180 (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 75557863725914323419393 else 151115727451828646838786) else (if j.val < 3 then 302231454903657293677572 else (if j.val < 4 then 604462909807314587355144 else 1208925819614629174710288))) else (if j.val < 8 then (if j.val < 6 then 2417851639229258349420576 else (if j.val < 7 then 4835703278458516698841152 else 9671406556917033397682304)) else (if j.val < 9 then 19342813113834066795364608 else (if j.val < 10 then 38685626227668133590729216 else 77371252455336267181458432)))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then 154742504910672534362916864 else 309485009821345068725833728) else (if j.val < 14 then 618970019642690137451667456 else (if j.val < 15 then 1152921504611057664 else 2305843009222115328))) else (if j.val < 19 then (if j.val < 17 then 4611686018444230656 else (if j.val < 18 then 9223372036888461312 else 18446744073776922624)) else (if j.val < 20 then 36893488147553845248 else (if j.val < 21 then 73786976295107690496 else 147573952590215380992))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then 295147905179357020161 else 590295810358714040322) else (if j.val < 25 then 1180591620717428080644 else (if j.val < 26 then 2361183241434856161288 else 4722366482869712322576))) else (if j.val < 30 then (if j.val < 28 then 9444732965739424645152 else (if j.val < 29 then 18889465931478849290304 else 37778931862957698580608)) else (if j.val < 31 then 81129638414606681696064956792832 else (if j.val < 32 then 162259276829213363392129913585664 else 324518553658426726784259827171328)))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then 649037107316853453568519654342656 else (if j.val < 35 then 1298074214633706907137039308685312 else 2596148429267413814274078617370624)) else (if j.val < 37 then 5192296858534827628548157234741248 else (if j.val < 38 then 10384593717069655257096314469482496 else 20769187434139310514192628938964992))) else (if j.val < 42 then (if j.val < 40 then 41538374868278621028385257877929984 else (if j.val < 41 then 83076749736557242056770515755859968 else 166153499473114484113541031511719936)) else (if j.val < 43 then 332306998946228968227082063023439872 else (if j.val < 44 then 664613997892457936454164126046879744 else 1237940039289901466712539136)))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then 2475880078579802933425078272 else 4951760157159605866850156544) else (if j.val < 48 then 9903520314319211733700313088 else (if j.val < 49 then 19807040628638423467400626176 else 39614081257276846934801252352))) else (if j.val < 53 then (if j.val < 51 then 79228162514553693869602504704 else (if j.val < 52 then 158456325029107387739205009408 else 316912650057061853974876913664)) else (if j.val < 54 then 633825300114123707949753827328 else (if j.val < 55 then 1267650600228247415899507654656 else 2535301200456494831799015309312)))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then 5070602400912989663598030618624 else 10141204801825979327196061237248) else (if j.val < 59 then 20282409603651958654392122474496 else (if j.val < 60 then 40564819207303917308784244948992 else 87112285931760246646920200329216621805568))) else (if j.val < 64 then (if j.val < 62 then 174224571863520493293840400658433243611136 else (if j.val < 63 then 348449143727040986587680801316866487222272 else 696898287454081973175361602633732974444544)) else (if j.val < 65 then 1393796574908163946350723205267465948889088 else (if j.val < 66 then 2787593149816327892701446410534931897778176 else 5575186299632655785402892821069863795556352))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then 11150372599265311570805785642139727591112704 else 22300745198530623141611571284279455182225408) else (if j.val < 70 then 44601490397061246283223142568558910364450816 else (if j.val < 71 then 89202980794122492566446285137117820728901632 else 178405961588244985132892570274235641457803264))) else (if j.val < 75 then (if j.val < 73 then 356811923176489970265785140548471282915606528 else (if j.val < 74 then 713623846352979940531570281096942565831213056 else 1329227995789770465648197055560024064)) else (if j.val < 76 then 2658455991579540931296394111120048128 else (if j.val < 77 then 5316911983159081862592788222240096256 else 10633823966318163725185576444480192512)))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then 21267647932636327450371152888960385024 else (if j.val < 80 then 42535295865272654900742305777920770048 else 85070591730545309801484611555841540096)) else (if j.val < 82 then 170141183461090619602969223111683080192 else (if j.val < 83 then 340282366920943299167805987453073883136 else 680564733841886598335611974906147766272))) else (if j.val < 87 then (if j.val < 85 then 1361129467683773196671223949812295532544 else (if j.val < 86 then 2722258935367546393342447899624591065088 else 5444517870735092786684895799249182130176)) else (if j.val < 88 then 10889035741470185573369791598498364260352 else (if j.val < 89 then 21778071482940371146739583196996728520704 else 43556142965880742293479166393993457041408))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then 93536104789177786765353979883938455988628757676032 else 187072209578355573530707959767876911977257515352064) else (if j.val < 93 then 374144419156711147061415919535753823954515030704128 else (if j.val < 94 then 748288838313422294122831839071507647909030061408256 else 1496577676626844588245663678143015295818060122816512))) else (if j.val < 98 then (if j.val < 96 then 2993155353253689176491327356286030591636120245633024 else (if j.val < 97 then 5986310706507378352982654712572061183272240491266048 else 11972621413014756705965309425144122366544480982532096)) else (if j.val < 99 then 23945242826029513411930618850288244733088961965064192 else (if j.val < 100 then 47890485652059026823861237700576489466177923930128384 else 95780971304118053647722475401152978932355847860256768)))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then 191561942608236107295444950802305957864711695720513536 else 383123885216472214590889901604611915729423391441027072) else (if j.val < 104 then 766247770432944429181779803209223831458846782882054144 else (if j.val < 105 then 1427247692711172460326424448748449579963252736 else 2854495385422344920652848897496899159926505472))) else (if j.val < 109 then (if j.val < 107 then 5708990770844689841305697794993798319853010944 else (if j.val < 108 then 11417981541689379682611395589987596639706021888 else 22835963083378759365222791179975193279412043776)) else (if j.val < 110 then 45671926166757518730445582359950386558824087552 else (if j.val < 111 then 91343852333515037460891164719900773117648175104 else 182687704667030074921782329439801546235296350208))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then 365375409332730921849017683045984665685211480064 else 730750818665461843698035366091969331370422960128) else (if j.val < 115 then 1461501637330923687396070732183938662740845920256 else (if j.val < 116 then 2923003274661847374792141464367877325481691840512 else 5846006549323694749584282928735754650963383681024))) else (if j.val < 120 then (if j.val < 118 then 11692013098647389499168565857471509301926767362048 else (if j.val < 119 then 23384026197294778998337131714943018603853534724096 else 46768052394589557996674263429886037207707069448192)) else (if j.val < 121 then 341611594916723379336278414492048621568 else (if j.val < 122 then 683223189833446758672556828984097243136 else 1366446379666893517345113657968194486272)))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then 2732892759333787034690227315936388972544 else (if j.val < 125 then 5465785518667574069380454631872777945088 else 10931571037335148138760909263745555890176)) else (if j.val < 127 then 21863142074670296277521818527491111780352 else (if j.val < 128 then 43726284149340592555043637054982223560704 else 87452568298681185110087274109964447121408))) else (if j.val < 132 then (if j.val < 130 then 174905136597362370220174548219928894242816 else (if j.val < 131 then 349810273194724740440349096439857788485632 else 699620546389449480880698192879715576971264)) else (if j.val < 133 then 1399241092778898961761396385759431153942528 else (if j.val < 134 then 2798482185557797923522792771518862307885056 else 5596964371115595847045585543037723542028289)))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then 11193928742231191694091171086075447084056578 else 22387857484462383388182342172150894168113156) else (if j.val < 138 then 44775714968924766776364684344301788336226312 else (if j.val < 139 then 89551429937849533552729368688603576672452624 else 179102859875699067105458737377207153344905248))) else (if j.val < 143 then (if j.val < 141 then 358205719751398134210917474754414306689810496 else (if j.val < 142 then 716411439502796268421834949508828613379620992 else 5575187628860651570299802471969150656839936)) else (if j.val < 144 then 11150375257721303140599604943938301313679872 else (if j.val < 145 then 22300750515442606281199209887876602627359744 else 44601501030885212562398419775753205254719488)))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then 89203002061770425124796839551506410509438976 else 178406004123540850249593679103012821018877952) else (if j.val < 149 then 356812008247081700499187358206025642037755904 else (if j.val < 150 then 713624016494163400998374716412051284075511808 else 366802657025431689431979494148520320419110060032))) else (if j.val < 154 then (if j.val < 152 then 733605314050863378863958988297040640838220120064 else (if j.val < 153 then 1467210628101726757727917976594081281676440240128 else 2934421256203453515455835953188162563352880480256)) else (if j.val < 155 then 5868842512406907030911671906376325126705760960512 else (if j.val < 156 then 11737685024813814061823343812752650253411521921024 else 23475370049627628123646687625505300506823043842048))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 46950740099255256247293375251010601013646087684096 else 93901480198510512494586750502021202027292175368192) else (if j.val < 160 then 187802960397021024989173501004042404054584350736384 else (if j.val < 161 then 375605920794042049978347002008084808109168701472768 else 751211841588084099956694004016169616218337402945536))) else (if j.val < 165 then (if j.val < 163 then 1502423683176168199913388008032339232436674805891072 else (if j.val < 164 then 3004847366352336399826776016064678464873349611782144 else 6009694732704672799653552032129355776825195690459136)) else (if j.val < 166 then 12019389465409345599307104064258711553650391380918272 else (if j.val < 167 then 24038778930818691198614208128517423107300782761836544 else 48077557861637382397228416257034846214601565523673088)))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then 96155115723274764794456832514069692429203131047346176 else (if j.val < 170 then 192310231446549529588913665028139384858406262094692352 else 384620462893099059177827330056278769716812524189384704)) else (if j.val < 172 then 769240925786198118355654660112557539433625048378769408 else (if j.val < 173 then 5986312133755071058922174133091864698006110956683264 else 11972624267510142117844348266183729396012221913366528))) else (if j.val < 177 then (if j.val < 175 then 23945248535020284235688696532367458792024443826733056 else (if j.val < 176 then 47890497070040568471377393064734917584048887653466112 else 95780994140081136942754786129469835168097775306932224)) else (if j.val < 178 then 191561988280162273885509572258939670336195550613864448 else (if j.val < 179 then 383123976560324547771019144517879340672391101227728896 else 766247953120649095542038289035758681344782202455457792)))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then 4294967299 else 8589934598) else (if j.val < 183 then 17179869196 else (if j.val < 184 then 34359738392 else 68719476784))) else (if j.val < 188 then (if j.val < 186 then 137438953568 else (if j.val < 187 then 274877907136 else 549755814272)) else (if j.val < 189 then 1099511628544 else (if j.val < 190 then 2199023257088 else 4398046514176)))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then 8796093028352 else 17592186056704) else (if j.val < 194 then 35184372113408 else (if j.val < 195 then 70368744226816 else 140737488453632))) else (if j.val < 199 then (if j.val < 197 then 281474976907264 else (if j.val < 198 then 562949953814528 else 1125899907629056)) else (if j.val < 200 then 2251799815258112 else (if j.val < 201 then 4503599630516224 else 9007199261032448))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then 18014398522064896 else 36028797044129792) else (if j.val < 205 then 72057594088259584 else (if j.val < 206 then 144115188176519168 else 288230376353038336))) else (if j.val < 210 then (if j.val < 208 then 576460752706076672 else (if j.val < 209 then 1879048192 else 2684354561)) else (if j.val < 211 then 4611686021648613376 else (if j.val < 212 then 9223372043297226752 else 18446744086594453504)))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then 36893488173188907008 else (if j.val < 215 then 73786976346377814016 else 147573952692755628032)) else (if j.val < 217 then 295147905385511256064 else (if j.val < 218 then 590295810771022512128 else 1180591621542045024256))) else (if j.val < 222 then (if j.val < 220 then 2361183243084090048512 else (if j.val < 221 then 4722366486168180097024 else 9444732972336360194048)) else (if j.val < 223 then 18889465944672720388096 else (if j.val < 224 then 37778931889345440776192 else 75557863778690881552384)))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then 151115727557381763104768 else 302231455114763526209536) else (if j.val < 228 then 604462910229527052419072 else (if j.val < 229 then 1208925820459054104838144 else 2417851640918108209676288))) else (if j.val < 233 then (if j.val < 231 then 4835703281836216419352576 else (if j.val < 232 then 9671406563672432838705152 else 19342813127344865677410304)) else (if j.val < 234 then 38685626254689731354820608 else (if j.val < 235 then 77371252509379462709641216 else 154742505018758925419282432)))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then 309485010037517850838564864 else 618970020075035701677129728) else (if j.val < 239 then 2017612633061982208 else (if j.val < 240 then 2882303762590859264 else 4951760160600285613417037824))) else (if j.val < 244 then (if j.val < 242 then 9903520321200571226834075648 else (if j.val < 243 then 19807040642401142453668151296 else 39614081284802284907336302592)) else (if j.val < 245 then 79228162569604569814672605184 else (if j.val < 246 then 158456325139209139629345210368 else 316912650278418279258690420736))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then 633825300556836558517380841472 else 1267650601113673117034761682944) else (if j.val < 250 then 2535301202227346234069523365888 else (if j.val < 251 then 5070602404454692468139046731776 else 10141204808909384936278093463552))) else (if j.val < 255 then (if j.val < 253 then 20282409617818769872556186927104 else (if j.val < 254 then 40564819235637539745112373854208 else 81129638471275079490224747708416)) else (if j.val < 256 then 162259276942550158980449495416832 else (if j.val < 257 then 324518553885100317960898990833664 else 649037107770200635921797981667328)))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then 1298074215540401271843595963334656 else (if j.val < 260 then 2596148431080802543687191926669312 else 5192296862161605087374383853338624)) else (if j.val < 262 then 10384593724323210174748767706677248 else (if j.val < 263 then 20769187448646420349497535413354496 else 41538374897292840698995070826708992))) else (if j.val < 267 then (if j.val < 265 then 83076749794585681397990141653417984 else (if j.val < 266 then 166153499589171362795980283306835968 else 332306999178342725591960566613671936)) else (if j.val < 268 then 664613998356685451183921133227343872 else (if j.val < 269 then 2166395068749415481073467392 else 3094850099366372191854657536))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then 5316911986853483609471369065818750976 else 10633823973706967218942738131637501952) else (if j.val < 273 then 21267647947413934437885476263275003904 else (if j.val < 274 then 42535295894827868875770952526550007808 else 85070591789655737751541905053100015616))) else (if j.val < 278 then (if j.val < 276 then 170141183579311475503083810106200031232 else (if j.val < 277 then 340282367158622951006167620212400062464 else 680564734317245902012335240424800124928)) else (if j.val < 279 then 1361129468634491804024670480849600249856 else (if j.val < 280 then 2722258937268983608049340961699200499712 else 5444517874537967216098681923398400999424)))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then 10889035749075934432197363846796801998848 else 21778071498151868864394727693593603997696) else (if j.val < 284 then 43556142996303737728789455387187207995392 else (if j.val < 285 then 87112285992607475457578910774374415990784 else 174224571985214950915157821548748831981568))) else (if j.val < 289 then (if j.val < 287 then 348449143970429901830315643097497663963136 else (if j.val < 288 then 696898287940859803660631286194995327926272 else 1393796575881719607321262572389990655852544)) else (if j.val < 290 then 2787593151763439214642525144779981311705088 else (if j.val < 291 then 5575186303526878429285050289559962623410176 else 11150372607053756858570100579119925246820352))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then 22300745214107513717140201158239850493640704 else 44601490428215027434280402316479700987281408) else (if j.val < 295 then 89202980856430054868560804632959401974562816 else (if j.val < 296 then 178405961712860109737121609265918803949125632 else 356811923425720219474243218531837607898251264))) else (if j.val < 300 then (if j.val < 298 then 713623846851440438948486437063675215796502528 else (if j.val < 299 then 2326148992623602777581662355490603008 else 3323069990700229721544897925599985664)) else (if j.val < 301 then 5708990774811523511587891496509401726372020224 else (if j.val < 302 then 11417981549623047023175782993018803452744040448 else 22835963099246094046351565986037606905488080896)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then 45671926198492188092703131972075213810976161792 else (if j.val < 305 then 91343852396984376185406263944150427621952323584 else 182687704793968752370812527888300855243904647168)) else (if j.val < 307 then 365375409587937504741625055776601710487809294336 else (if j.val < 308 then 730750819175875009483250111553203420975618588672 else 1461501638351750018966500223106406841951237177344))) else (if j.val < 312 then (if j.val < 310 then 2923003276703500037933000446212813683902474354688 else (if j.val < 311 then 5846006553407000075866000892425627367804948709376 else 11692013106814000151732001784851254735609897418752)) else (if j.val < 313 then 23384026213628000303464003569702509471219794837504 else (if j.val < 314 then 46768052427256000606928007139405018942439589675008 else 93536104854512001213856014278810037884879179350016)))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 187072209709024002427712028557620075769758358700032 else 374144419418048004855424057115240151539516717400064) else (if j.val < 318 then 748288838836096009710848114230480303079033434800128 else (if j.val < 319 then 1496577677672192019421696228460960606158066869600256 else 2993155355344384038843392456921921212316133739200512))) else (if j.val < 323 then (if j.val < 321 then 5986310710688768077686784913843842424632267478401024 else (if j.val < 322 then 11972621421377536155373569827687684849264534956802048 else 23945242842755072310747139655375369698529069913604096)) else (if j.val < 324 then 47890485685510144621494279310750739397058139827208192 else (if j.val < 325 then 95780971371020289242988558621501478794116279654416384 else 191561942742040578485977117243002957588232559308832768)))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then 383123885484081156971954234486005915176465118617665536 else 766247770968162313943908468972011830352930237235331072) else (if j.val < 329 then 2497683462235429791852000446536616488669806592 else (if j.val < 330 then 3568119233094127698430630796527544901237211136 else 4281743078117879643174857908348485409148239876))) else (if j.val < 334 then (if j.val < 332 then 8563486156235759286349715816696970818296479752 else (if j.val < 333 then 17126972312471518572699431633393941636592959504 else 34253944624943037145398863266787883273185919008)) else (if j.val < 335 then 68507889249886074290797726533575766546371838016 else (if j.val < 336 then 137015778499772148581595453067151533092743676032 else 274031556999544297163190906134303066185487352064))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then 548063113999088594326381812268606132370974704128 else 1096126227998177188652763624537212264741949408256) else (if j.val < 340 then 2192252455996354377305527249074424529483898816512 else (if j.val < 341 then 4384504911992708754611054498148849058967797633024 else 8769009823985417509222108996297698117935595266048))) else (if j.val < 345 then (if j.val < 343 then 17538019647970835018444217992595396235871190532096 else (if j.val < 344 then 35076039295941670036888435985190792471742381064192 else 70152078591883340073776871970381584943484762128384)) else (if j.val < 346 then 140304157183766680147553743940763169886969524256768 else (if j.val < 347 then 280608314367533360295107487881526339773939048513536 else 561216628735066720590214975763052679547878097027072)))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then 1122433257470133441180429951526105359095756194054144 else (if j.val < 350 then 2244866514940266882360859903052210718191512388108288 else 4489733029880533764721719806104421436383024776216576)) else (if j.val < 352 then 8979466059761067529443439612208842872766049552433152 else (if j.val < 353 then 17958932119522135058886879224417685745532099104866304 else 35917864239044270117773758448835371491064198209732608))) else (if j.val < 357 then (if j.val < 355 then 71835728478088540235547516897670742982128396419465216 else (if j.val < 356 then 143671456956177080471095033795341485964256792838930432 else 287342913912354160942190067590682971928513585677860864)) else (if j.val < 358 then 574685827824708321884380135181365943857027171355721728 else (if j.val < 359 then 1149371655649416643768760270362731887714054341637701633 else 766247771860192121885133394633440561258864697474547714)))))))))
def zH : Matrix (Fin 180) (Fin 360) (ZMod 2) := fun i j => entry (zmask j) i
end BBNew360KernelData

set_option maxHeartbeats 0
open Matrix BBCode
namespace BBNew360Symmetry

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
    have he := (BBNew360Cert.rowspace_reindex (HX A B) negG dualQ v)
    rw [HX_dual] at he
    exact hv.2 (he.mp h)
end BBNew360Symmetry

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BBNew360Cert BBNew360Bits
namespace BBNew360KernelData
def polyA : Poly 6 30 := {(0,0),(0,1),(1,2)}
def polyB : Poly 6 30 := {(0,0),(0,8),(2,16)}
def er : Fin 180 ≃ Grp 6 30 where
  toFun i := ((i.val / 30 : ℕ), (i.val % 30 : ℕ))
  invFun g := ⟨g.1.val * 30 + g.2.val, by
    have h1 := ZMod.val_lt g.1
    have h2 := ZMod.val_lt g.2
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eqb : Fin 360 ≃ Qubit 6 30 where
  toFun i := if h : i.val < 180 then Sum.inl (er ⟨i.val,h⟩)
    else Sum.inr (er ⟨i.val-180,by omega⟩)
  invFun q := match q with
    | Sum.inl g => ⟨(er.symm g).val, by have h := (er.symm g).isLt; omega⟩
    | Sum.inr g => ⟨180 + (er.symm g).val, by have h := (er.symm g).isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

namespace BBNew360Sparse

lemma col_three (a b c g : Grp 6 30) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 180) :
    circulant {a,b,c} (er i) g =
      entry (unit (er.symm (g-a)) ^^^ unit (er.symm (g-b)) ^^^ unit (er.symm (g-c))) i := by
  have eqg (t : Grp 6 30) : i = er.symm (g-t) ↔ g-er i = t := by
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

def column (q : Qubit 6 30) : BitVec 180 :=
  match q with
  | Sum.inl g => unit (er.symm (g-(0,0))) ^^^ unit (er.symm (g-(0,1))) ^^^ unit (er.symm (g-(1,2)))
  | Sum.inr g => unit (er.symm (g-(0,0))) ^^^ unit (er.symm (g-(0,8))) ^^^ unit (er.symm (g-(2,16)))

lemma column_entry (i : Fin 180) (q : Qubit 6 30) :
    HX polyA polyB (er i) q = entry (column q) i := by
  cases q with
  | inl g => exact col_three (0,0) (0,1) (1,2) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three (0,0) (0,8) (2,16) g (by decide) (by decide) (by decide) i

lemma xcolumn_bits : ∀ j, xmask j = column (eqb j) := by decide +kernel
lemma xtable_sparse : (HX polyA polyB).submatrix er eqb = xH := by
  ext i j
  change HX polyA polyB (er i) (eqb j) = entry (xmask j) i
  rw [xcolumn_bits,column_entry]
end BBNew360Sparse

namespace BBNew360Sparse
lemma col_three_z (a b c g : Grp 6 30) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 180) :
    circulant {a,b,c} g (er i) =
      entry (unit (er.symm (g+a)) ^^^ unit (er.symm (g+b)) ^^^ unit (er.symm (g+c))) i := by
  have eqg (t : Grp 6 30) : i = er.symm (g+t) ↔ er i-g = t := by
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


def zcolumn (q : Qubit 6 30) : BitVec 180 :=
  match q with
  | Sum.inl g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,8))) ^^^ unit (er.symm (g+(2,16)))
  | Sum.inr g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,1))) ^^^ unit (er.symm (g+(1,2)))

lemma zcolumn_entry (i : Fin 180) (q : Qubit 6 30) :
    HZ polyA polyB (er i) q = entry (zcolumn q) i := by
  cases q with
  | inl g => exact col_three_z (0,0) (0,8) (2,16) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three_z (0,0) (0,1) (1,2) g (by decide) (by decide) (by decide) i

lemma zcolumn_bits : ∀ j, zmask j = zcolumn (eqb j) := by decide +kernel
lemma ztable_sparse : (HZ polyA polyB).submatrix er eqb = zH := by
  ext i j
  change HZ polyA polyB (er i) (eqb j) = entry (zmask j) i
  rw [zcolumn_bits,zcolumn_entry]
end BBNew360Sparse

lemma xtable : (HX polyA polyB).submatrix er eqb = xH := BBNew360Sparse.xtable_sparse
lemma ztable : (HZ polyA polyB).submatrix er eqb = zH := BBNew360Sparse.ztable_sparse
lemma xcolParity : ∀ j, ∑ i, xH i j = 1 := by
  intro j
  change ∑ i, entry (xmask j) i = 1
  rw [BBNew360Sparse.xcolumn_bits]
  cases hq : eqb j with
  | inl g => simp [BBNew360Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
  | inr g => simp [BBNew360Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
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
def rowFormula (i : Fin 180) : BitVec 360 :=
  unit (eqb.symm (Sum.inl (er i+(0,0)))) ^^^
  unit (eqb.symm (Sum.inl (er i+(0,1)))) ^^^
  unit (eqb.symm (Sum.inl (er i+(1,2)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,0)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,8)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(2,16))))
lemma row_formula_bits : ∀ i, xrow i = rowFormula i := by decide +kernel
lemma row_formula_entry (i : Fin 180) (j : Fin 360) :
    entry (rowFormula i) j = HX polyA polyB (er i) (eqb j) := by
  cases hq : eqb j with
  | inl g =>
    have yes (t : Grp 6 30) : j = eqb.symm (Sum.inl (er i+t)) ↔ g-er i = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inl.injEq,sub_eq_iff_eq_add,add_comm]
    have no (t : Grp 6 30) : j ≠ eqb.symm (Sum.inr (er i+t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [rowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HX,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,1) (1,2) (g-er i) (by decide) (by decide) (by decide)
  | inr g =>
    have yes (t : Grp 6 30) : j = eqb.symm (Sum.inr (er i+t)) ↔ g-er i = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inr.injEq,sub_eq_iff_eq_add,add_comm]
    have no (t : Grp 6 30) : j ≠ eqb.symm (Sum.inl (er i+t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [rowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HX,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,8) (2,16) (g-er i) (by decide) (by decide) (by decide)
lemma xrow_entry (i : Fin 180) (j : Fin 360) : entry (xrow i) j = xH i j := by
  rw [row_formula_bits,row_formula_entry]
  exact congrFun (congrFun xtable i) j
end BBNew360KernelData

set_option maxHeartbeats 0
open Matrix BBCode BBNew360Cert
namespace BBNew360Peel
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
end BBNew360Peel

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BBNew360Cert
namespace BBNew360Search

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
end BBNew360Search

set_option maxHeartbeats 0
open BBNew360Search
namespace BBNew360Count
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
end BBNew360Count

set_option maxHeartbeats 0
namespace BBNew360High

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
end BBNew360High

namespace BBNew360KernelData
open BBNew360Search
def xneighbors (i : Fin 180) : List (Fin 360) := (if i.val < 90 then (if i.val < 45 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [0, 1, 32, 180, 188, 256] else [1, 2, 33, 181, 189, 257]) else (if i.val < 3 then [2, 3, 34, 182, 190, 258] else (if i.val < 4 then [3, 4, 35, 183, 191, 259] else [4, 5, 36, 184, 192, 260]))) else (if i.val < 8 then (if i.val < 6 then [5, 6, 37, 185, 193, 261] else (if i.val < 7 then [6, 7, 38, 186, 194, 262] else [7, 8, 39, 187, 195, 263])) else (if i.val < 9 then [8, 9, 40, 188, 196, 264] else (if i.val < 10 then [9, 10, 41, 189, 197, 265] else [10, 11, 42, 190, 198, 266])))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then [11, 12, 43, 191, 199, 267] else [12, 13, 44, 192, 200, 268]) else (if i.val < 14 then [13, 14, 45, 193, 201, 269] else (if i.val < 15 then [14, 15, 46, 194, 202, 240] else [15, 16, 47, 195, 203, 241]))) else (if i.val < 19 then (if i.val < 17 then [16, 17, 48, 196, 204, 242] else (if i.val < 18 then [17, 18, 49, 197, 205, 243] else [18, 19, 50, 198, 206, 244])) else (if i.val < 20 then [19, 20, 51, 199, 207, 245] else (if i.val < 21 then [20, 21, 52, 200, 208, 246] else [21, 22, 53, 201, 209, 247]))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then [22, 23, 54, 180, 202, 248] else [23, 24, 55, 181, 203, 249]) else (if i.val < 25 then [24, 25, 56, 182, 204, 250] else (if i.val < 26 then [25, 26, 57, 183, 205, 251] else [26, 27, 58, 184, 206, 252]))) else (if i.val < 30 then (if i.val < 28 then [27, 28, 59, 185, 207, 253] else (if i.val < 29 then [28, 29, 30, 186, 208, 254] else [0, 29, 31, 187, 209, 255])) else (if i.val < 31 then [30, 31, 62, 210, 218, 286] else (if i.val < 32 then [31, 32, 63, 211, 219, 287] else [32, 33, 64, 212, 220, 288])))) else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then [33, 34, 65, 213, 221, 289] else (if i.val < 35 then [34, 35, 66, 214, 222, 290] else [35, 36, 67, 215, 223, 291])) else (if i.val < 37 then [36, 37, 68, 216, 224, 292] else (if i.val < 38 then [37, 38, 69, 217, 225, 293] else [38, 39, 70, 218, 226, 294]))) else (if i.val < 42 then (if i.val < 40 then [39, 40, 71, 219, 227, 295] else (if i.val < 41 then [40, 41, 72, 220, 228, 296] else [41, 42, 73, 221, 229, 297])) else (if i.val < 43 then [42, 43, 74, 222, 230, 298] else (if i.val < 44 then [43, 44, 75, 223, 231, 299] else [44, 45, 76, 224, 232, 270])))))) else (if i.val < 67 then (if i.val < 56 then (if i.val < 50 then (if i.val < 47 then (if i.val < 46 then [45, 46, 77, 225, 233, 271] else [46, 47, 78, 226, 234, 272]) else (if i.val < 48 then [47, 48, 79, 227, 235, 273] else (if i.val < 49 then [48, 49, 80, 228, 236, 274] else [49, 50, 81, 229, 237, 275]))) else (if i.val < 53 then (if i.val < 51 then [50, 51, 82, 230, 238, 276] else (if i.val < 52 then [51, 52, 83, 231, 239, 277] else [52, 53, 84, 210, 232, 278])) else (if i.val < 54 then [53, 54, 85, 211, 233, 279] else (if i.val < 55 then [54, 55, 86, 212, 234, 280] else [55, 56, 87, 213, 235, 281])))) else (if i.val < 61 then (if i.val < 58 then (if i.val < 57 then [56, 57, 88, 214, 236, 282] else [57, 58, 89, 215, 237, 283]) else (if i.val < 59 then [58, 59, 60, 216, 238, 284] else (if i.val < 60 then [30, 59, 61, 217, 239, 285] else [60, 61, 92, 240, 248, 316]))) else (if i.val < 64 then (if i.val < 62 then [61, 62, 93, 241, 249, 317] else (if i.val < 63 then [62, 63, 94, 242, 250, 318] else [63, 64, 95, 243, 251, 319])) else (if i.val < 65 then [64, 65, 96, 244, 252, 320] else (if i.val < 66 then [65, 66, 97, 245, 253, 321] else [66, 67, 98, 246, 254, 322]))))) else (if i.val < 78 then (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then [67, 68, 99, 247, 255, 323] else [68, 69, 100, 248, 256, 324]) else (if i.val < 70 then [69, 70, 101, 249, 257, 325] else (if i.val < 71 then [70, 71, 102, 250, 258, 326] else [71, 72, 103, 251, 259, 327]))) else (if i.val < 75 then (if i.val < 73 then [72, 73, 104, 252, 260, 328] else (if i.val < 74 then [73, 74, 105, 253, 261, 329] else [74, 75, 106, 254, 262, 300])) else (if i.val < 76 then [75, 76, 107, 255, 263, 301] else (if i.val < 77 then [76, 77, 108, 256, 264, 302] else [77, 78, 109, 257, 265, 303])))) else (if i.val < 84 then (if i.val < 81 then (if i.val < 79 then [78, 79, 110, 258, 266, 304] else (if i.val < 80 then [79, 80, 111, 259, 267, 305] else [80, 81, 112, 260, 268, 306])) else (if i.val < 82 then [81, 82, 113, 261, 269, 307] else (if i.val < 83 then [82, 83, 114, 240, 262, 308] else [83, 84, 115, 241, 263, 309]))) else (if i.val < 87 then (if i.val < 85 then [84, 85, 116, 242, 264, 310] else (if i.val < 86 then [85, 86, 117, 243, 265, 311] else [86, 87, 118, 244, 266, 312])) else (if i.val < 88 then [87, 88, 119, 245, 267, 313] else (if i.val < 89 then [88, 89, 90, 246, 268, 314] else [60, 89, 91, 247, 269, 315]))))))) else (if i.val < 135 then (if i.val < 112 then (if i.val < 101 then (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then [90, 91, 122, 270, 278, 346] else [91, 92, 123, 271, 279, 347]) else (if i.val < 93 then [92, 93, 124, 272, 280, 348] else (if i.val < 94 then [93, 94, 125, 273, 281, 349] else [94, 95, 126, 274, 282, 350]))) else (if i.val < 98 then (if i.val < 96 then [95, 96, 127, 275, 283, 351] else (if i.val < 97 then [96, 97, 128, 276, 284, 352] else [97, 98, 129, 277, 285, 353])) else (if i.val < 99 then [98, 99, 130, 278, 286, 354] else (if i.val < 100 then [99, 100, 131, 279, 287, 355] else [100, 101, 132, 280, 288, 356])))) else (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then [101, 102, 133, 281, 289, 357] else [102, 103, 134, 282, 290, 358]) else (if i.val < 104 then [103, 104, 135, 283, 291, 359] else (if i.val < 105 then [104, 105, 136, 284, 292, 330] else [105, 106, 137, 285, 293, 331]))) else (if i.val < 109 then (if i.val < 107 then [106, 107, 138, 286, 294, 332] else (if i.val < 108 then [107, 108, 139, 287, 295, 333] else [108, 109, 140, 288, 296, 334])) else (if i.val < 110 then [109, 110, 141, 289, 297, 335] else (if i.val < 111 then [110, 111, 142, 290, 298, 336] else [111, 112, 143, 291, 299, 337]))))) else (if i.val < 123 then (if i.val < 117 then (if i.val < 114 then (if i.val < 113 then [112, 113, 144, 270, 292, 338] else [113, 114, 145, 271, 293, 339]) else (if i.val < 115 then [114, 115, 146, 272, 294, 340] else (if i.val < 116 then [115, 116, 147, 273, 295, 341] else [116, 117, 148, 274, 296, 342]))) else (if i.val < 120 then (if i.val < 118 then [117, 118, 149, 275, 297, 343] else (if i.val < 119 then [118, 119, 120, 276, 298, 344] else [90, 119, 121, 277, 299, 345])) else (if i.val < 121 then [120, 121, 152, 196, 300, 308] else (if i.val < 122 then [121, 122, 153, 197, 301, 309] else [122, 123, 154, 198, 302, 310])))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 124 then [123, 124, 155, 199, 303, 311] else (if i.val < 125 then [124, 125, 156, 200, 304, 312] else [125, 126, 157, 201, 305, 313])) else (if i.val < 127 then [126, 127, 158, 202, 306, 314] else (if i.val < 128 then [127, 128, 159, 203, 307, 315] else [128, 129, 160, 204, 308, 316]))) else (if i.val < 132 then (if i.val < 130 then [129, 130, 161, 205, 309, 317] else (if i.val < 131 then [130, 131, 162, 206, 310, 318] else [131, 132, 163, 207, 311, 319])) else (if i.val < 133 then [132, 133, 164, 208, 312, 320] else (if i.val < 134 then [133, 134, 165, 209, 313, 321] else [134, 135, 166, 180, 314, 322])))))) else (if i.val < 157 then (if i.val < 146 then (if i.val < 140 then (if i.val < 137 then (if i.val < 136 then [135, 136, 167, 181, 315, 323] else [136, 137, 168, 182, 316, 324]) else (if i.val < 138 then [137, 138, 169, 183, 317, 325] else (if i.val < 139 then [138, 139, 170, 184, 318, 326] else [139, 140, 171, 185, 319, 327]))) else (if i.val < 143 then (if i.val < 141 then [140, 141, 172, 186, 320, 328] else (if i.val < 142 then [141, 142, 173, 187, 321, 329] else [142, 143, 174, 188, 300, 322])) else (if i.val < 144 then [143, 144, 175, 189, 301, 323] else (if i.val < 145 then [144, 145, 176, 190, 302, 324] else [145, 146, 177, 191, 303, 325])))) else (if i.val < 151 then (if i.val < 148 then (if i.val < 147 then [146, 147, 178, 192, 304, 326] else [147, 148, 179, 193, 305, 327]) else (if i.val < 149 then [148, 149, 150, 194, 306, 328] else (if i.val < 150 then [120, 149, 151, 195, 307, 329] else [2, 150, 151, 226, 330, 338]))) else (if i.val < 154 then (if i.val < 152 then [3, 151, 152, 227, 331, 339] else (if i.val < 153 then [4, 152, 153, 228, 332, 340] else [5, 153, 154, 229, 333, 341])) else (if i.val < 155 then [6, 154, 155, 230, 334, 342] else (if i.val < 156 then [7, 155, 156, 231, 335, 343] else [8, 156, 157, 232, 336, 344]))))) else (if i.val < 168 then (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then [9, 157, 158, 233, 337, 345] else [10, 158, 159, 234, 338, 346]) else (if i.val < 160 then [11, 159, 160, 235, 339, 347] else (if i.val < 161 then [12, 160, 161, 236, 340, 348] else [13, 161, 162, 237, 341, 349]))) else (if i.val < 165 then (if i.val < 163 then [14, 162, 163, 238, 342, 350] else (if i.val < 164 then [15, 163, 164, 239, 343, 351] else [16, 164, 165, 210, 344, 352])) else (if i.val < 166 then [17, 165, 166, 211, 345, 353] else (if i.val < 167 then [18, 166, 167, 212, 346, 354] else [19, 167, 168, 213, 347, 355])))) else (if i.val < 174 then (if i.val < 171 then (if i.val < 169 then [20, 168, 169, 214, 348, 356] else (if i.val < 170 then [21, 169, 170, 215, 349, 357] else [22, 170, 171, 216, 350, 358])) else (if i.val < 172 then [23, 171, 172, 217, 351, 359] else (if i.val < 173 then [24, 172, 173, 218, 330, 352] else [25, 173, 174, 219, 331, 353]))) else (if i.val < 177 then (if i.val < 175 then [26, 174, 175, 220, 332, 354] else (if i.val < 176 then [27, 175, 176, 221, 333, 355] else [28, 176, 177, 222, 334, 356])) else (if i.val < 178 then [29, 177, 178, 223, 335, 357] else (if i.val < 179 then [0, 178, 179, 224, 336, 358] else [1, 150, 179, 225, 337, 359]))))))))
def xpos (j : Fin 360) : List (Fin 180) := (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [0, 29, 178] else [0, 1, 179]) else (if j.val < 3 then [1, 2, 150] else (if j.val < 4 then [2, 3, 151] else [3, 4, 152]))) else (if j.val < 8 then (if j.val < 6 then [4, 5, 153] else (if j.val < 7 then [5, 6, 154] else [6, 7, 155])) else (if j.val < 9 then [7, 8, 156] else (if j.val < 10 then [8, 9, 157] else [9, 10, 158])))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then [10, 11, 159] else [11, 12, 160]) else (if j.val < 14 then [12, 13, 161] else (if j.val < 15 then [13, 14, 162] else [14, 15, 163]))) else (if j.val < 19 then (if j.val < 17 then [15, 16, 164] else (if j.val < 18 then [16, 17, 165] else [17, 18, 166])) else (if j.val < 20 then [18, 19, 167] else (if j.val < 21 then [19, 20, 168] else [20, 21, 169]))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then [21, 22, 170] else [22, 23, 171]) else (if j.val < 25 then [23, 24, 172] else (if j.val < 26 then [24, 25, 173] else [25, 26, 174]))) else (if j.val < 30 then (if j.val < 28 then [26, 27, 175] else (if j.val < 29 then [27, 28, 176] else [28, 29, 177])) else (if j.val < 31 then [28, 30, 59] else (if j.val < 32 then [29, 30, 31] else [0, 31, 32])))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then [1, 32, 33] else (if j.val < 35 then [2, 33, 34] else [3, 34, 35])) else (if j.val < 37 then [4, 35, 36] else (if j.val < 38 then [5, 36, 37] else [6, 37, 38]))) else (if j.val < 42 then (if j.val < 40 then [7, 38, 39] else (if j.val < 41 then [8, 39, 40] else [9, 40, 41])) else (if j.val < 43 then [10, 41, 42] else (if j.val < 44 then [11, 42, 43] else [12, 43, 44])))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then [13, 44, 45] else [14, 45, 46]) else (if j.val < 48 then [15, 46, 47] else (if j.val < 49 then [16, 47, 48] else [17, 48, 49]))) else (if j.val < 53 then (if j.val < 51 then [18, 49, 50] else (if j.val < 52 then [19, 50, 51] else [20, 51, 52])) else (if j.val < 54 then [21, 52, 53] else (if j.val < 55 then [22, 53, 54] else [23, 54, 55])))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then [24, 55, 56] else [25, 56, 57]) else (if j.val < 59 then [26, 57, 58] else (if j.val < 60 then [27, 58, 59] else [58, 60, 89]))) else (if j.val < 64 then (if j.val < 62 then [59, 60, 61] else (if j.val < 63 then [30, 61, 62] else [31, 62, 63])) else (if j.val < 65 then [32, 63, 64] else (if j.val < 66 then [33, 64, 65] else [34, 65, 66]))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then [35, 66, 67] else [36, 67, 68]) else (if j.val < 70 then [37, 68, 69] else (if j.val < 71 then [38, 69, 70] else [39, 70, 71]))) else (if j.val < 75 then (if j.val < 73 then [40, 71, 72] else (if j.val < 74 then [41, 72, 73] else [42, 73, 74])) else (if j.val < 76 then [43, 74, 75] else (if j.val < 77 then [44, 75, 76] else [45, 76, 77])))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then [46, 77, 78] else (if j.val < 80 then [47, 78, 79] else [48, 79, 80])) else (if j.val < 82 then [49, 80, 81] else (if j.val < 83 then [50, 81, 82] else [51, 82, 83]))) else (if j.val < 87 then (if j.val < 85 then [52, 83, 84] else (if j.val < 86 then [53, 84, 85] else [54, 85, 86])) else (if j.val < 88 then [55, 86, 87] else (if j.val < 89 then [56, 87, 88] else [57, 88, 89]))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then [88, 90, 119] else [89, 90, 91]) else (if j.val < 93 then [60, 91, 92] else (if j.val < 94 then [61, 92, 93] else [62, 93, 94]))) else (if j.val < 98 then (if j.val < 96 then [63, 94, 95] else (if j.val < 97 then [64, 95, 96] else [65, 96, 97])) else (if j.val < 99 then [66, 97, 98] else (if j.val < 100 then [67, 98, 99] else [68, 99, 100])))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then [69, 100, 101] else [70, 101, 102]) else (if j.val < 104 then [71, 102, 103] else (if j.val < 105 then [72, 103, 104] else [73, 104, 105]))) else (if j.val < 109 then (if j.val < 107 then [74, 105, 106] else (if j.val < 108 then [75, 106, 107] else [76, 107, 108])) else (if j.val < 110 then [77, 108, 109] else (if j.val < 111 then [78, 109, 110] else [79, 110, 111]))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then [80, 111, 112] else [81, 112, 113]) else (if j.val < 115 then [82, 113, 114] else (if j.val < 116 then [83, 114, 115] else [84, 115, 116]))) else (if j.val < 120 then (if j.val < 118 then [85, 116, 117] else (if j.val < 119 then [86, 117, 118] else [87, 118, 119])) else (if j.val < 121 then [118, 120, 149] else (if j.val < 122 then [119, 120, 121] else [90, 121, 122])))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then [91, 122, 123] else (if j.val < 125 then [92, 123, 124] else [93, 124, 125])) else (if j.val < 127 then [94, 125, 126] else (if j.val < 128 then [95, 126, 127] else [96, 127, 128]))) else (if j.val < 132 then (if j.val < 130 then [97, 128, 129] else (if j.val < 131 then [98, 129, 130] else [99, 130, 131])) else (if j.val < 133 then [100, 131, 132] else (if j.val < 134 then [101, 132, 133] else [102, 133, 134])))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then [103, 134, 135] else [104, 135, 136]) else (if j.val < 138 then [105, 136, 137] else (if j.val < 139 then [106, 137, 138] else [107, 138, 139]))) else (if j.val < 143 then (if j.val < 141 then [108, 139, 140] else (if j.val < 142 then [109, 140, 141] else [110, 141, 142])) else (if j.val < 144 then [111, 142, 143] else (if j.val < 145 then [112, 143, 144] else [113, 144, 145])))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then [114, 145, 146] else [115, 146, 147]) else (if j.val < 149 then [116, 147, 148] else (if j.val < 150 then [117, 148, 149] else [148, 150, 179]))) else (if j.val < 154 then (if j.val < 152 then [149, 150, 151] else (if j.val < 153 then [120, 151, 152] else [121, 152, 153])) else (if j.val < 155 then [122, 153, 154] else (if j.val < 156 then [123, 154, 155] else [124, 155, 156]))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then [125, 156, 157] else [126, 157, 158]) else (if j.val < 160 then [127, 158, 159] else (if j.val < 161 then [128, 159, 160] else [129, 160, 161]))) else (if j.val < 165 then (if j.val < 163 then [130, 161, 162] else (if j.val < 164 then [131, 162, 163] else [132, 163, 164])) else (if j.val < 166 then [133, 164, 165] else (if j.val < 167 then [134, 165, 166] else [135, 166, 167])))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then [136, 167, 168] else (if j.val < 170 then [137, 168, 169] else [138, 169, 170])) else (if j.val < 172 then [139, 170, 171] else (if j.val < 173 then [140, 171, 172] else [141, 172, 173]))) else (if j.val < 177 then (if j.val < 175 then [142, 173, 174] else (if j.val < 176 then [143, 174, 175] else [144, 175, 176])) else (if j.val < 178 then [145, 176, 177] else (if j.val < 179 then [146, 177, 178] else [147, 178, 179])))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then [0, 22, 134] else [1, 23, 135]) else (if j.val < 183 then [2, 24, 136] else (if j.val < 184 then [3, 25, 137] else [4, 26, 138]))) else (if j.val < 188 then (if j.val < 186 then [5, 27, 139] else (if j.val < 187 then [6, 28, 140] else [7, 29, 141])) else (if j.val < 189 then [0, 8, 142] else (if j.val < 190 then [1, 9, 143] else [2, 10, 144])))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then [3, 11, 145] else [4, 12, 146]) else (if j.val < 194 then [5, 13, 147] else (if j.val < 195 then [6, 14, 148] else [7, 15, 149]))) else (if j.val < 199 then (if j.val < 197 then [8, 16, 120] else (if j.val < 198 then [9, 17, 121] else [10, 18, 122])) else (if j.val < 200 then [11, 19, 123] else (if j.val < 201 then [12, 20, 124] else [13, 21, 125]))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then [14, 22, 126] else [15, 23, 127]) else (if j.val < 205 then [16, 24, 128] else (if j.val < 206 then [17, 25, 129] else [18, 26, 130]))) else (if j.val < 210 then (if j.val < 208 then [19, 27, 131] else (if j.val < 209 then [20, 28, 132] else [21, 29, 133])) else (if j.val < 211 then [30, 52, 164] else (if j.val < 212 then [31, 53, 165] else [32, 54, 166])))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then [33, 55, 167] else (if j.val < 215 then [34, 56, 168] else [35, 57, 169])) else (if j.val < 217 then [36, 58, 170] else (if j.val < 218 then [37, 59, 171] else [30, 38, 172]))) else (if j.val < 222 then (if j.val < 220 then [31, 39, 173] else (if j.val < 221 then [32, 40, 174] else [33, 41, 175])) else (if j.val < 223 then [34, 42, 176] else (if j.val < 224 then [35, 43, 177] else [36, 44, 178])))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then [37, 45, 179] else [38, 46, 150]) else (if j.val < 228 then [39, 47, 151] else (if j.val < 229 then [40, 48, 152] else [41, 49, 153]))) else (if j.val < 233 then (if j.val < 231 then [42, 50, 154] else (if j.val < 232 then [43, 51, 155] else [44, 52, 156])) else (if j.val < 234 then [45, 53, 157] else (if j.val < 235 then [46, 54, 158] else [47, 55, 159])))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then [48, 56, 160] else [49, 57, 161]) else (if j.val < 239 then [50, 58, 162] else (if j.val < 240 then [51, 59, 163] else [14, 60, 82]))) else (if j.val < 244 then (if j.val < 242 then [15, 61, 83] else (if j.val < 243 then [16, 62, 84] else [17, 63, 85])) else (if j.val < 245 then [18, 64, 86] else (if j.val < 246 then [19, 65, 87] else [20, 66, 88]))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then [21, 67, 89] else [22, 60, 68]) else (if j.val < 250 then [23, 61, 69] else (if j.val < 251 then [24, 62, 70] else [25, 63, 71]))) else (if j.val < 255 then (if j.val < 253 then [26, 64, 72] else (if j.val < 254 then [27, 65, 73] else [28, 66, 74])) else (if j.val < 256 then [29, 67, 75] else (if j.val < 257 then [0, 68, 76] else [1, 69, 77])))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then [2, 70, 78] else (if j.val < 260 then [3, 71, 79] else [4, 72, 80])) else (if j.val < 262 then [5, 73, 81] else (if j.val < 263 then [6, 74, 82] else [7, 75, 83]))) else (if j.val < 267 then (if j.val < 265 then [8, 76, 84] else (if j.val < 266 then [9, 77, 85] else [10, 78, 86])) else (if j.val < 268 then [11, 79, 87] else (if j.val < 269 then [12, 80, 88] else [13, 81, 89]))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then [44, 90, 112] else [45, 91, 113]) else (if j.val < 273 then [46, 92, 114] else (if j.val < 274 then [47, 93, 115] else [48, 94, 116]))) else (if j.val < 278 then (if j.val < 276 then [49, 95, 117] else (if j.val < 277 then [50, 96, 118] else [51, 97, 119])) else (if j.val < 279 then [52, 90, 98] else (if j.val < 280 then [53, 91, 99] else [54, 92, 100])))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then [55, 93, 101] else [56, 94, 102]) else (if j.val < 284 then [57, 95, 103] else (if j.val < 285 then [58, 96, 104] else [59, 97, 105]))) else (if j.val < 289 then (if j.val < 287 then [30, 98, 106] else (if j.val < 288 then [31, 99, 107] else [32, 100, 108])) else (if j.val < 290 then [33, 101, 109] else (if j.val < 291 then [34, 102, 110] else [35, 103, 111]))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then [36, 104, 112] else [37, 105, 113]) else (if j.val < 295 then [38, 106, 114] else (if j.val < 296 then [39, 107, 115] else [40, 108, 116]))) else (if j.val < 300 then (if j.val < 298 then [41, 109, 117] else (if j.val < 299 then [42, 110, 118] else [43, 111, 119])) else (if j.val < 301 then [74, 120, 142] else (if j.val < 302 then [75, 121, 143] else [76, 122, 144])))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then [77, 123, 145] else (if j.val < 305 then [78, 124, 146] else [79, 125, 147])) else (if j.val < 307 then [80, 126, 148] else (if j.val < 308 then [81, 127, 149] else [82, 120, 128]))) else (if j.val < 312 then (if j.val < 310 then [83, 121, 129] else (if j.val < 311 then [84, 122, 130] else [85, 123, 131])) else (if j.val < 313 then [86, 124, 132] else (if j.val < 314 then [87, 125, 133] else [88, 126, 134])))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then [89, 127, 135] else [60, 128, 136]) else (if j.val < 318 then [61, 129, 137] else (if j.val < 319 then [62, 130, 138] else [63, 131, 139]))) else (if j.val < 323 then (if j.val < 321 then [64, 132, 140] else (if j.val < 322 then [65, 133, 141] else [66, 134, 142])) else (if j.val < 324 then [67, 135, 143] else (if j.val < 325 then [68, 136, 144] else [69, 137, 145])))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then [70, 138, 146] else [71, 139, 147]) else (if j.val < 329 then [72, 140, 148] else (if j.val < 330 then [73, 141, 149] else [104, 150, 172]))) else (if j.val < 334 then (if j.val < 332 then [105, 151, 173] else (if j.val < 333 then [106, 152, 174] else [107, 153, 175])) else (if j.val < 335 then [108, 154, 176] else (if j.val < 336 then [109, 155, 177] else [110, 156, 178]))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then [111, 157, 179] else [112, 150, 158]) else (if j.val < 340 then [113, 151, 159] else (if j.val < 341 then [114, 152, 160] else [115, 153, 161]))) else (if j.val < 345 then (if j.val < 343 then [116, 154, 162] else (if j.val < 344 then [117, 155, 163] else [118, 156, 164])) else (if j.val < 346 then [119, 157, 165] else (if j.val < 347 then [90, 158, 166] else [91, 159, 167])))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then [92, 160, 168] else (if j.val < 350 then [93, 161, 169] else [94, 162, 170])) else (if j.val < 352 then [95, 163, 171] else (if j.val < 353 then [96, 164, 172] else [97, 165, 173]))) else (if j.val < 357 then (if j.val < 355 then [98, 166, 174] else (if j.val < 356 then [99, 167, 175] else [100, 168, 176])) else (if j.val < 358 then [101, 169, 177] else (if j.val < 359 then [102, 170, 178] else [103, 171, 179])))))))))
lemma xpos_nodup : ∀ j, (xpos j).Nodup := by decide +kernel
lemma xpos_signature : ∀ j, signature unit (xpos j) = xmask j := by decide +kernel
lemma xpos_length : ∀ j, (xpos j).length = 3 := by decide +kernel
lemma entry_nonzero_iff {r : ℕ} (v : BitVec r) (i : Fin r) :
    entry v i ≠ 0 ↔ v.getLsbD i.val = true := by
  unfold entry
  cases v.getLsbD i.val <;> decide
lemma xpos_spec (j : Fin 360) : (xpos j).Nodup ∧ (xpos j).toFinset = Finset.univ.filter (fun i => (xmask j).getLsbD i.val) := by
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
lemma xthree (j : Fin 360) : ones (xmask j) = 3 := by
  rw [ones_card,← (xpos_spec j).2,List.toFinset_card_of_nodup (xpos_nodup j),xpos_length]
def xupdate (j : Fin 360) (sy : BitVec 180) (pc : ℕ) : ℕ :=
  pc + 3 - 2 * ((xpos j).map fun i => (sy.getLsbD i.val).toNat).sum
lemma xupdate_spec (j : Fin 360) (sy : BitVec 180) : xupdate j sy (ones sy) = ones (xmask j ^^^ sy) :=
  BBNew360Count.update_eq (xmask j) sy (xpos j) (xpos_spec j).1 (xpos_spec j).2 (xthree j)
lemma xones (j : Fin 360) : ones (xmask j) ≤ 3 := (xthree j).le
lemma xpos_cover : ∀ j, (xpos j).all (fun i => decide (j ∈ xneighbors i)) = true := by decide +kernel
lemma xcover (i : Fin 180) (j : Fin 360) (h : entry (xmask j) i = 1) : j ∈ xneighbors i := by
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

lemma unindex_kernel (H : Matrix (Grp 6 30) (Qubit 6 30) (ZMod 2))
    (v : Fin 360 → ZMod 2) (hv : H.submatrix er eqb *ᵥ v = 0) :
    H *ᵥ (v ∘ eqb.symm) = 0 := by
  have h := Matrix.submatrix_mulVec_equiv H v er eqb
  rw [hv] at h
  funext i
  have hi := congrFun h (er.symm i)
  simpa using hi.symm

lemma index_kernel (H : Matrix (Grp 6 30) (Qubit 6 30) (ZMod 2))
    (v : Qubit 6 30 → ZMod 2) (hv : H *ᵥ v = 0) :
    H.submatrix er eqb *ᵥ (v ∘ eqb) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ eqb) ∘ eqb.symm = v := by funext i; simp
  rw [he,hv]
  rfl

end BBNew360KernelData

namespace BBNew360KernelData
lemma xnonzero : ∀ j, xmask j ≠ 0 := by decide +kernel
end BBNew360KernelData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BBNew360Cert BBNew360KernelData
namespace BBNew360Peel
section
variable (left : ∀ (v : Qubit 6 30 → ZMod 2), HX polyA polyB *ᵥ v = 0 → weight v ≤ 10 →
    v (Sum.inl (0,0)) ≠ 0 → ∃ u : Qubit 6 30 → ZMod 2,
      HX polyA polyB *ᵥ u = 0 ∧ u ∈ rowSpace (HZ polyA polyB) ∧
      u (Sum.inl (0,0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0)
variable (right : ∀ (v : Qubit 6 30 → ZMod 2), HX polyA polyB *ᵥ v = 0 → weight v ≤ 10 →
    v (Sum.inr (0,0)) ≠ 0 → ∃ u : Qubit 6 30 → ZMod 2,
      HX polyA polyB *ᵥ u = 0 ∧ u ∈ rowSpace (HZ polyA polyB) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0)
include left right
lemma close (v : Qubit 6 30 → ZMod 2) (hv : HX polyA polyB *ᵥ v = 0)
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
    suffices ∀ g : Grp 6 30, (v (Sum.inl g) ≠ 0 ∨ v (Sum.inr g) ≠ 0) →
        v ∈ rowSpace (HZ polyA polyB) by
      cases q with
      | inl g => exact this g (Or.inl hq)
      | inr g => exact this g (Or.inr hq)
    intro g ha
    let w := v ∘ BBNew360Symmetry.shiftQ g
    have hwker : HX polyA polyB *ᵥ w = 0 := by
      have h := BBNew360Symmetry.kernel_reindex (HX polyA polyB)
        (BBNew360Symmetry.shiftG g) (BBNew360Symmetry.shiftQ g) v hv
      rwa [BBNew360Symmetry.HX_shift] at h
    have hweq : weight w = weight v := BBNew360Symmetry.weight_equiv _ v
    have hwW : weight w ≤ 10 := by omega
    have hwr : w ∈ rowSpace (HZ polyA polyB) := by
      have peel : ∀ (anchor : Qubit 6 30) (u : Qubit 6 30 → ZMod 2),
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
          change v (Sum.inl ((0 : Grp 6 30) + g)) ≠ 0
          simpa only [zero_add] using ha
        obtain ⟨u,huk,hum,hua,hus⟩ := left w hwker hwW hanchor
        exact peel (Sum.inl (0,0)) u huk hum hua hus
      · have hanchor : w (Sum.inr (0,0)) ≠ 0 := by
          change v (Sum.inr ((0 : Grp 6 30) + g)) ≠ 0
          simpa only [zero_add] using ha
        obtain ⟨u,huk,hum,hua,hus⟩ := right w hwker hwW hanchor
        exact peel (Sum.inr (0,0)) u huk hum hua hus
    have he := rowspace_reindex (HZ polyA polyB)
      (BBNew360Symmetry.shiftG g) (BBNew360Symmetry.shiftQ g) v
    rw [BBNew360Symmetry.HZ_shift] at he
    exact he.mp hwr
end
end BBNew360Peel

open Matrix BBCode BBNew360Cert BBNew360KernelData BBNew360Search
namespace BBNew360Other
lemma exists_other (anchor : Fin 360) (v : Fin 360 → ZMod 2)
    (ha : v anchor ≠ 0) (hv : xH *ᵥ v = 0) :
    ∃ j ∈ xneighbors (BBNew360High.pick (xmask anchor)), j ≠ anchor ∧ v j ≠ 0 := by
  classical
  let T := Finset.univ.filter fun j => v j ≠ 0
  let i := BBNew360High.pick (xmask anchor)
  have hp : entry (xmask anchor) i = 1 := by
    simp [entry,i,BBNew360High.pick_spec _ (xnonzero anchor)]
  have hT : ∑ j ∈ T, entry (xmask j) i = 0 := by
    change ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), xH i j = 0
    rw [← support_mul xH v i,hv]
    rfl
  have hu : ({anchor} : Finset (Fin 360)) ⊆ T := by simpa [T] using ha
  have hex : ∃ j ∈ T, j ≠ anchor ∧ entry (xmask j) i = 1 := by
    by_contra hnot
    have he : ∑ j ∈ ({anchor} : Finset (Fin 360)), entry (xmask j) i = ∑ j ∈ T, entry (xmask j) i := by
      apply Finset.sum_subset hu
      intro j hj hjn
      by_contra hne
      exact hnot ⟨j,hj,by simpa using hjn,binary_eq_one hne⟩
    simp only [Finset.sum_singleton,hT,hp] at he
    exact one_ne_zero he
  obtain ⟨j,hj,hne,hji⟩ := hex
  exact ⟨j,xcover i j hji,hne,by simpa [T] using hj⟩
end BBNew360Other

namespace BBNew360DistanceReduce
lemma complete (v : Qubit 6 30 → ZMod 2) (hv : HX polyA polyB *ᵥ v = 0)
    (hw : weight v ≤ 10) : v ∈ rowSpace (HZ polyA polyB) := by
  apply BBNew360Peel.close ?_ ?_ v hv hw
  · intro w hwker hwW haW
    have hwi : xH *ᵥ (w ∘ eqb) = 0 := by
      rw [← xtable]
      exact index_kernel _ w hwker
    have hanchor : (w ∘ eqb) 0 ≠ 0 := by
      simpa only [Function.comp_apply,show eqb (0 : Fin 360) = (Sum.inl (0,0)) from by decide +kernel] using haW
    obtain ⟨j,hj,hne,hvj⟩ := BBNew360Other.exists_other 0 (w ∘ eqb) hanchor hwi
    have hn : xneighbors (BBNew360High.pick (xmask (0 : Fin 360))) = [0, 178, 179, 224, 336, 358] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hne rfl)
    · apply BBCode.new360_support_left_companion178 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (178 : Fin 360) = (Sum.inl (5,28)) from by decide +kernel] using hvj
    · apply BBCode.new360_support_left_companion179 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (179 : Fin 360) = (Sum.inl (5,29)) from by decide +kernel] using hvj
    · apply BBCode.new360_support_left_companion224 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (224 : Fin 360) = (Sum.inr (1,14)) from by decide +kernel] using hvj
    · apply BBCode.new360_support_left_companion336 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (336 : Fin 360) = (Sum.inr (5,6)) from by decide +kernel] using hvj
    · apply BBCode.new360_support_left_companion358 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (358 : Fin 360) = (Sum.inr (5,28)) from by decide +kernel] using hvj
  · intro w hwker hwW haW
    have hwi : xH *ᵥ (w ∘ eqb) = 0 := by
      rw [← xtable]
      exact index_kernel _ w hwker
    have hanchor : (w ∘ eqb) 180 ≠ 0 := by
      simpa only [Function.comp_apply,show eqb (180 : Fin 360) = (Sum.inr (0,0)) from by decide +kernel] using haW
    obtain ⟨j,hj,hne,hvj⟩ := BBNew360Other.exists_other 180 (w ∘ eqb) hanchor hwi
    have hn : xneighbors (BBNew360High.pick (xmask (180 : Fin 360))) = [134, 135, 166, 180, 314, 322] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · apply BBCode.new360_support_right_companion134 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (134 : Fin 360) = (Sum.inl (4,14)) from by decide +kernel] using hvj
    · apply BBCode.new360_support_right_companion135 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (135 : Fin 360) = (Sum.inl (4,15)) from by decide +kernel] using hvj
    · apply BBCode.new360_support_right_companion166 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (166 : Fin 360) = (Sum.inl (5,16)) from by decide +kernel] using hvj
    · exact False.elim (hne rfl)
    · apply BBCode.new360_support_right_companion314 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (314 : Fin 360) = (Sum.inr (4,14)) from by decide +kernel] using hvj
    · apply BBCode.new360_support_right_companion322 w hwker hwW haW
      simpa only [Function.comp_apply,show eqb (322 : Fin 360) = (Sum.inr (4,22)) from by decide +kernel] using hvj
end BBNew360DistanceReduce
theorem solution (v : BBCode.Qubit 6 30 → ZMod 2)
    (hv : BBCode.HX (l := 6) (m := 30) {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10) :
    v ∈ BBCode.rowSpace (BBCode.HZ (l := 6) (m := 30)
      {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)}) := BBNew360DistanceReduce.complete v hv hw

#print axioms solution
