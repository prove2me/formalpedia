-- Prove2me | solution 1 for ConvexOptAlg.SVRG.unbiased_direction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:07:30.100632+00:00
-- url     : https://prove2.me/submissions/5aab1a8e-6bc5-4b0c-aef9-08e728f1d3d9

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

open scoped InnerProductSpace

namespace SVRGUnbiasedHelp

theorem grad_ineq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g x z : EuclideanSpace ℝ (Fin n))
    (hf : HasGradientAt f g x) (hc : ConvexOn ℝ Set.univ f) :
    f x + ⟪g, z - x⟫_ℝ ≤ f z := by
  set l : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x z with hl
  have hφ : ConvexOn ℝ Set.univ (f ∘ l) := by
    simpa using hc.comp_affineMap l
  have hl0 : l 0 = x := by simp [hl]
  have hl1 : l 1 = z := by simp [hl]
  have hld : HasDerivAt (fun t : ℝ => l t) (z - x) 0 := by
    have := AffineMap.hasDerivAt_lineMap (a := x) (b := z) (x := (0:ℝ))
    simpa [hl, vsub_eq_sub] using this
  have hfd : HasFDerivAt f (InnerProductSpace.toDual ℝ _ g) (l 0) := by
    rw [hl0]; exact hf.hasFDerivAt
  have hd : HasDerivAt (f ∘ l) ⟪g, z - x⟫_ℝ 0 := by
    have := hfd.comp_hasDerivAt (0:ℝ) hld
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  simp only [Function.comp_apply, hl0, hl1, sub_zero, div_one] at this
  linarith

end SVRGUnbiasedHelp

-- The unnumbered display after (6.3), p. 337: the SVRG direction is unbiased,
-- and convexity bounds its pairing with the displacement from `xstar`.
open ConvexOptAlg.SVRG in open scoped InnerProductSpace in
theorem solution {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ⟪direction gs x y i, x - xstar⟫_ℝ) =
      ⟪fullGradient gs x, x - xstar⟫_ℝ ∧
    objective fs x - objective fs xstar ≤
      ⟪fullGradient gs x, x - xstar⟫_ℝ := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · unfold uniformMean direction fullGradient
    simp only [inner_add_left, inner_sub_left, inner_smul_left, sum_inner,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, RCLike.conj_to_real]
    field_simp
    ring
  · unfold objective uniformMean fullGradient
    rw [inner_smul_left, sum_inner, RCLike.conj_to_real, Fintype.card_fin]
    have key : ∀ i, fs i x - fs i xstar ≤ ⟪gs i x, x - xstar⟫_ℝ := by
      intro i
      have := SVRGUnbiasedHelp.grad_ineq (fs i) (gs i x) x xstar (hfamily.1 i x) (hfamily.2.1 i)
      have h2 : ⟪gs i x, xstar - x⟫_ℝ = -⟪gs i x, x - xstar⟫_ℝ := by
        rw [← inner_neg_right, neg_sub]
      linarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
    rw [Finset.sum_sub_distrib] at hsum
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm
    rw [← sub_div, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hmpos.le)
