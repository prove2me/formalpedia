-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_exists_quadraticAt_expansion_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:16.593672+00:00
-- url     : https://prove2.me/submissions/97268921-afe3-4007-a917-ecd2fc6f3437

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Theorems.Thm_FunctionalInequalities_Analysis_ae_exists_secondOrder_expansion_readable

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12D6BAeMongeAmpere
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
/-- **Alexandrov's theorem in coordinates** (weak Letwin route): a convex function on
`EuclideanSpace ℝ (Fin n)` has, at almost every point `x`, a second-order expansion
`|u y − quadraticAt B x g (u x) y| ≤ ε ‖y − x‖²` near `x` with a symmetric matrix `B`. -/
theorem solution {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ ∃ g : EuclideanSpace ℝ (Fin n),
        ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - FunctionalInequalities.Analysis.quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion_readable hconv] with x hx
  rcases hx with ⟨p, B, hsym, _, hexp⟩
  let A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.toEuclideanLin.symm
      (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hA : Matrix.toEuclideanLin A =
      (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hHermitian : A.IsHermitian := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [hA]
    exact hsym
  have hquad (v : EuclideanSpace ℝ (Fin n)) :
      ⟪v, Matrix.toEuclideanLin A v⟫ = ⟪B v, v⟫ := by
    rw [hA]
    exact real_inner_comm (B v) v
  refine ⟨A, hHermitian, p, ?_⟩
  intro ε hε
  filter_upwards [hexp ε hε] with y hy
  simpa only [FunctionalInequalities.Analysis.quadraticAt, hquad, sub_add_eq_sub_sub] using hy
