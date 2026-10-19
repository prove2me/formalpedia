-- Prove2me | solution 1 for CauchyRiemannIndex.linearIndependent_sub_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:02:58.679046+00:00
-- url     : https://prove2.me/submissions/6ca67932-cea2-4d0e-8e52-1e99de5735d6

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs



/-!
# Small perturbations of an orthogonal family
-/

namespace CauchyRiemannIndex

open scoped RealInnerProductSpace

/-- Perturbations of an orthogonal family by small vectors stay independent. -/
lemma lap_indep {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V W : ι → H) (L ε : ℝ) (hVV : ∀ i j, i ≠ j → ⟪V j, V i⟫ = 0)
    (hVn : ∀ i, L ≤ ‖V i‖ ^ 2) (hW : ∀ i, ‖W i‖ ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) ^ 2 * ε ^ 2 < L) :
    LinearIndependent ℝ fun i => V i - W i := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hrow : ∀ j, c j * ‖V j‖ ^ 2 = ∑ i, c i * ⟪W i, V j⟫ := by
    intro j
    have h := congrArg (fun y => ⟪y, V j⟫) hc
    simp only [inner_zero_left, sum_inner, inner_smul_left, inner_sub_left,
      RCLike.conj_to_real, mul_sub, Finset.sum_sub_distrib] at h
    have hs : ∑ i, c i * ⟪V i, V j⟫ = c j * ‖V j‖ ^ 2 := by
      rw [Finset.sum_eq_single j (fun i _ hi => by rw [hVV j i (Ne.symm hi), mul_zero])
        (fun h => absurd (Finset.mem_univ j) h), real_inner_self_eq_norm_sq]
    linarith
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|)
    ⟨i₀, Finset.mem_univ _⟩
  have hcj : 0 < |c j| := lt_of_lt_of_le (abs_pos.2 hi₀) (hj i₀ (Finset.mem_univ _))
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hW j)
  have hL : 0 < L := lt_of_le_of_lt (by positivity) hsmall
  have hVpos : 0 < ‖V j‖ := by
    have h0 : 0 < ‖V j‖ ^ 2 := hL.trans_le (hVn j)
    by_contra h
    push Not at h
    have : ‖V j‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this] at h0; simp at h0
  have hbound : |c j| * ‖V j‖ ^ 2 ≤ Fintype.card ι * |c j| * ε * ‖V j‖ := by
    rw [← abs_of_pos (by positivity : 0 < ‖V j‖ ^ 2), ← abs_mul, hrow j]
    calc |∑ i, c i * ⟪W i, V j⟫| ≤ ∑ i, |c i * ⟪W i, V j⟫| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, |c j| * (ε * ‖V j‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hj i (Finset.mem_univ _)) ?_ (abs_nonneg _) (abs_nonneg _)
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hW i) (norm_nonneg _))
      _ = Fintype.card ι * |c j| * ε * ‖V j‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h1 : ‖V j‖ ≤ Fintype.card ι * ε := by
    have h' : (|c j| * ‖V j‖) * ‖V j‖ ≤ (|c j| * (Fintype.card ι * ε)) * ‖V j‖ := by
      nlinarith
    exact le_of_mul_le_mul_left (le_of_mul_le_mul_right h' hVpos) hcj
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow] at h2
  linarith [hVn j]

end CauchyRiemannIndex

open CauchyRiemannIndex

open scoped RealInnerProductSpace

theorem solution {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (V W : ι → H) (L ε : ℝ) (hVV : ∀ i j, i ≠ j → ⟪V j, V i⟫ = 0)
    (hVn : ∀ i, L ≤ ‖V i‖ ^ 2) (hW : ∀ i, ‖W i‖ ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) ^ 2 * ε ^ 2 < L) :
    LinearIndependent ℝ fun i => V i - W i :=
  lap_indep V W L ε hVV hVn hW hsmall
