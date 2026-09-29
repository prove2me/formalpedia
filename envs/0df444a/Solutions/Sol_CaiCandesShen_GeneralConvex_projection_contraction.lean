-- Prove2me | solution 1 for CaiCandesShen.GeneralConvex.projection_contraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:04:21.732595+00:00
-- url     : https://prove2.me/submissions/784d29b9-3604-498d-a489-cca126f19e3d

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

theorem aux_pc_dot_add_single {m : ℕ} (u v : Fin m → ℝ) (i : Fin m) (c : ℝ) :
    dot (u + Pi.single i c) v = dot u v + c * v i := by
  unfold dot
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem aux_pc_eucNorm_mono {m : ℕ} (u v : Fin m → ℝ) (h : ∀ i, |u i| ≤ |v i|) :
    eucNorm u ≤ eucNorm v := by
  unfold eucNorm dot
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact abs_le_iff_mul_self_le.mp (h i)

theorem aux_pc_comp_slack {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys)
    (d : ℝ) (hd : 0 ≤ d) (i : Fin m) :
    max (ys i + d * constraintMap f Xs i) 0 = ys i := by
  obtain ⟨hnn, hmax, _⟩ := hopt
  set F := constraintMap f Xs with hF
  -- F i ≤ 0
  have h1 : F i ≤ 0 := by
    have := hmax (ys + Pi.single i 1) (by
      intro j
      by_cases hj : j = i
      · subst hj; simp; linarith [hnn j]
      · simp [hj, hnn j])
    unfold lagr at this
    rw [aux_pc_dot_add_single] at this
    linarith
  -- ys i * F i ≥ 0
  have h2 : 0 ≤ ys i * F i := by
    have := hmax (ys + Pi.single i (-ys i)) (by
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj, hnn j])
    unfold lagr at this
    rw [aux_pc_dot_add_single] at this
    linarith
  have hy := hnn i
  rcases eq_or_lt_of_le hy with h0 | hpos
  · rw [← h0]
    apply max_eq_right
    have : d * F i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd h1
    linarith
  · have hF0 : F i = 0 := by
      have : 0 ≤ F i := by
        by_contra hc
        rw [not_le] at hc
        have := mul_neg_of_pos_of_neg hpos hc
        linarith
      linarith
    rw [hF0, mul_zero, add_zero]
    exact max_eq_left hy

end CaiCandesShen.GeneralConvex

open CaiCandesShen.GeneralConvex

theorem solution {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (δ : ℕ → ℝ) (hδ : ∀ k : ℕ, 1 ≤ k → 0 < δ k)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    ∀ k : ℕ, eucNorm (y (k + 1) - ys) ≤ eucNorm (y k - ys +
      δ (k + 1) • (constraintMap f (X (k + 1)) - constraintMap f Xs)) := by
  intro k
  apply aux_pc_eucNorm_mono
  intro i
  have hd : 0 ≤ δ (k + 1) := le_of_lt (hδ (k + 1) (by omega))
  have hys := aux_pc_comp_slack τ f Xs ys hopt (δ (k + 1)) hd i
  have hyk := hseq.2.2 k i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hyk]
  conv_lhs => rw [← hys]
  have := abs_max_sub_max_le_abs (y k i + δ (k + 1) * constraintMap f (X (k + 1)) i)
    (ys i + δ (k + 1) * constraintMap f Xs i) 0
  calc _ ≤ _ := this
    _ = _ := by congr 1; ring
