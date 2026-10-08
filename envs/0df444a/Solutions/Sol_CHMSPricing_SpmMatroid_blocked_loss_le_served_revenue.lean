-- Prove2me | solution 1 for CHMSPricing.SpmMatroid.blocked_loss_le_served_revenue
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:15:02.795253+00:00
-- url     : https://prove2.me/submissions/6839b06e-f003-4b25-9120-53c9f30f15d1

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm



namespace CHMSPricing.SpmMatroid
open MeasureTheory Set

namespace MatAux
variable {n : ℕ}
lemma A_succ (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : ℕ)
    (hk : k < n) :
    spmServedBefore J σ p v (k+1) = spmStep J p v (spmServedBefore J σ p v k) (σ ⟨k, hk⟩) := by
  have htake : (List.finRange n).take (k+1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
    rw [List.take_add_one]
    congr 1
    simp [hk]
  unfold spmServedBefore
  rw [htake, List.foldl_append]
  rfl

lemma A_zero (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) :
    spmServedBefore J σ p v 0 = ∅ := by simp [spmServedBefore]

lemma A_dep (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v w : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) (h : ∀ j : Fin n, j.val < k → (p (σ j) ≤ v (σ j) ↔ p (σ j) ≤ w (σ j))) :
    spmServedBefore J σ p v k = spmServedBefore J σ p w k := by
  induction k with
  | zero => rw [A_zero, A_zero]
  | succ k ih =>
    rw [A_succ J σ p v k hk, A_succ J σ p w k hk, ih (by omega) (fun j hj => h j (by omega))]
    have hiff := h ⟨k, hk⟩ (by simp)
    unfold spmStep
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)

lemma A_feas (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) : J.Feasible (spmServedBefore J σ p v k) := by
  induction k with
  | zero => rw [A_zero]; exact J.feasible_empty
  | succ k ih =>
    rw [A_succ J σ p v k hk]
    unfold spmStep
    split_ifs with h
    · exact h.1
    · exact ih (by omega)

lemma A_mem (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (j : Fin n)
    (m : ℕ) (hm : m ≤ n) :
    σ j ∈ spmServedBefore J σ p v m ↔ j.val < m ∧ σ j ∈ spmServedBefore J σ p v (j.val+1) := by
  induction m with
  | zero => simp [A_zero]
  | succ m ih =>
    have hmn : m < n := hm
    rw [A_succ J σ p v m hmn]
    unfold spmStep
    rcases lt_trichotomy j.val m with hjm | hjm | hjm
    · have hne : σ j ≠ σ ⟨m, hmn⟩ := fun e => by
        have := congrArg Fin.val (σ.injective e); simp at this; omega
      have := ih hmn.le
      split_ifs <;> simp only [Finset.mem_insert, hne, false_or, this] <;>
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
    · have hj : j = ⟨m, hmn⟩ := Fin.ext hjm
      subst hj
      rw [A_succ J σ p v m hmn]
      unfold spmStep
      simp
    · have hne : σ j ≠ σ ⟨m, hmn⟩ := fun e => by
        have := congrArg Fin.val (σ.injective e); simp at this; omega
      have := ih hmn.le
      split_ifs <;> simp only [Finset.mem_insert, hne, false_or, this] <;>
        constructor <;> rintro ⟨h1, h2⟩ <;> omega

lemma A_mono (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k m : ℕ)
    (hkm : k ≤ m) (hm : m ≤ n) :
    spmServedBefore J σ p v k ⊆ spmServedBefore J σ p v m := by
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this; exact subset_rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hkm with h | h
    · rw [h]
    · refine (ih (by omega) (by omega)).trans ?_
      rw [A_succ J σ p v m (by omega)]
      unfold spmStep
      split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_rfl

lemma abel_nonneg (a d : ℕ → ℝ) (ha : ∀ k, a (k+1) ≤ a k) (ha0 : ∀ k, 0 ≤ a k)
    (N : ℕ) (hD : ∀ m ≤ N, 0 ≤ ∑ k ∈ Finset.range m, d k) :
    0 ≤ ∑ k ∈ Finset.range N, a k * d k := by
  have key : ∀ M ≤ N, a M * ∑ k ∈ Finset.range M, d k ≤ ∑ k ∈ Finset.range M, a k * d k := by
    intro M
    induction M with
    | zero => intro _; simp
    | succ M ih =>
      intro hM
      have h1 := ih (by omega)
      have h2 := hD (M+1) hM
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_range_succ] at h2
      have : a (M+1) * (∑ k ∈ Finset.range M, d k + d M) ≤
          a M * (∑ k ∈ Finset.range M, d k + d M) := mul_le_mul_of_nonneg_right (ha M) h2
      nlinarith
  exact le_trans (mul_nonneg (ha0 N) (hD N le_rfl)) (key N le_rfl)

/-- extension of a `Fin n`-indexed function to `ℕ` by zero -/
noncomputable def ext (g : Fin n → ℝ) (k : ℕ) : ℝ := if h : k < n then g ⟨k, h⟩ else 0

lemma sum_prefix (g : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ k : Fin n, (if k.val < m then g k else 0) = ∑ k ∈ Finset.range m, ext g k := by
  have h1 := Fin.sum_univ_eq_sum_range (fun k => if k < m then ext g k else 0) n
  have h2 : ∑ k : Fin n, (if k.val < m then g k else 0) =
      ∑ k : Fin n, (if k.val < m then ext g k.val else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [ext]
  rw [h2, h1, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext k; simp [Finset.mem_filter]; omega

lemma sum_all (g : Fin n → ℝ) : ∑ k : Fin n, g k = ∑ k ∈ Finset.range n, ext g k := by
  rw [← sum_prefix g n le_rfl]
  simp

/-- prefix inequality -/
lemma prefix_ineq (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ i ∈ (spmBlocked J σ p v).filter (fun i => (σ.symm i).val < m), q i ≤
      ((spmServedBefore J σ p v m).card : ℝ) := by
  classical
  set Am := spmServedBefore J σ p v m with hAm
  set Bm := (spmBlocked J σ p v).filter (fun i => (σ.symm i).val < m) with hBm
  have hrank : J.rank (Am ∪ Bm) ≤ Am.card := by
    unfold SetSystem.rank
    refine Finset.sup_le (fun F hF => ?_)
    rw [Finset.mem_filter, Finset.mem_powerset] at hF
    by_contra hlt
    push_neg at hlt
    obtain ⟨e, he, hfe⟩ := hJ F Am hF.2 (A_feas J σ p v m hm) hlt
    rw [Finset.mem_sdiff] at he
    have heB : e ∈ Bm := by
      rcases Finset.mem_union.1 (hF.1 he.1) with h | h
      · exact absurd h he.2
      · exact h
    rw [hBm, Finset.mem_filter] at heB
    have hbl : ¬ J.Feasible (insert e (spmServedBefore J σ p v (σ.symm e : ℕ))) := by
      have := heB.1
      simp only [spmBlocked, spmOffered] at this
      exact (Finset.mem_filter.1 this).2
    exact hbl (J.feasible_mono (Finset.insert_subset_insert _
      (A_mono J σ p v _ m heB.2.le hm)) hfe)
  calc ∑ i ∈ Bm, q i ≤ ∑ i ∈ Am ∪ Bm, q i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun i _ _ => hq0 i)
    _ ≤ (J.rank (Am ∪ Bm) : ℝ) := hqr _
    _ ≤ Am.card := by exact_mod_cast hrank

theorem blocked_core (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) (v : Fin n → ℝ) :
    ∑ i ∈ spmBlocked J σ p v, p i * q i ≤
      ∑ i ∈ spmServed J σ p v, p i := by
  classical
  set B := spmBlocked J σ p v
  set A := spmServed J σ p v
  let x : Fin n → ℝ := fun k => if σ k ∈ B then q (σ k) else 0
  let y : Fin n → ℝ := fun k => if σ k ∈ A then 1 else 0
  let pk : Fin n → ℝ := fun k => p (σ k)
  have hL : ∑ i ∈ B, p i * q i = ∑ k : Fin n, pk k * x k := by
    rw [← Finset.univ_inter B, ← Finset.sum_ite_mem, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [pk, x, mul_ite, mul_zero]
  have hR : ∑ i ∈ A, p i = ∑ k : Fin n, pk k * y k := by
    rw [← Finset.univ_inter A, ← Finset.sum_ite_mem, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [pk, y, mul_ite, mul_zero, mul_one]
  have hext : ∀ g h : Fin n → ℝ, ∑ k : Fin n, g k * h k =
      ∑ k ∈ Finset.range n, ext g k * ext h k := by
    intro g h
    rw [sum_all (fun k => g k * h k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold ext; split_ifs <;> simp
  have hX : ∀ m ≤ n, ∑ k ∈ Finset.range m, ext x k =
      ∑ i ∈ B.filter (fun i => (σ.symm i).val < m), q i := by
    intro m hm
    rw [← sum_prefix x m hm, ← Finset.univ_inter (B.filter _), ← Finset.sum_ite_mem]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [x, Finset.mem_filter, Equiv.symm_apply_apply]
    split_ifs <;> tauto
  have hY : ∀ m ≤ n, ∑ k ∈ Finset.range m, ext y k =
      ((spmServedBefore J σ p v m).card : ℝ) := by
    intro m hm
    rw [← sum_prefix y m hm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      ← Finset.univ_inter (spmServedBefore J σ p v m), ← Finset.sum_ite_mem]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [y, A, spmServed]
    have h1 := A_mem J σ p v k m hm
    have h2 := A_mem J σ p v k n le_rfl
    simp only [k.isLt, true_and] at h2
    by_cases c1 : (k : ℕ) < m <;> by_cases c2 : σ k ∈ spmServedBefore J σ p v n <;>
      simp only [c1, c2, if_true, if_false] <;> simp_all
  have key := abel_nonneg (ext pk) (fun k => ext y k - ext x k) (by
      intro k
      unfold ext
      split_ifs with h1 h2
      · exact hσ _ _ (Fin.mk_le_mk.2 (by omega))
      · omega
      · exact hp0 _
      · exact le_rfl)
    (by intro k; unfold ext; split_ifs <;> simp [pk, hp0]) n (by
      intro m hm
      rw [Finset.sum_sub_distrib, hX m hm, hY m hm, sub_nonneg]
      exact prefix_ineq J hJ q hq0 hqr σ p v m hm)
  rw [hL, hR, hext, hext]
  simp only [mul_sub, Finset.sum_sub_distrib, sub_nonneg] at key
  exact key

end MatAux
end CHMSPricing.SpmMatroid

open CHMSPricing.SpmMatroid


theorem solution {n : ℕ} (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) (v : Fin n → ℝ) :
    ∑ i ∈ spmBlocked J σ p v, p i * q i ≤
      ∑ i ∈ spmServed J σ p v, p i := by
  exact MatAux.blocked_core J hJ q hq0 hqr σ p hp0 hσ v
