-- Prove2me | solution 1 for FunctionalInequalities.Analysis.posSemidef_hessianMatrix_of_upper_touch_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:08.815172+00:00
-- url     : https://prove2.me/submissions/e13adf37-9edf-4841-9f01-5867661d3dce

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Theorems.Thm_FunctionalInequalities_Analysis_directional_second_deriv_nonneg_readable

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
/-- **A `C²` function touching a convex function from above has positive semidefinite Hessian at the
contact point** (weak Letwin route, viscosity tests). -/
theorem solution {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    (FunctionalInequalities.Probability.Stein.hessianMatrix ψ x₀).PosSemidef := by
  classical
  have hs := hψ.isSymmSndFDerivAt
    (by norm_num : minSmoothness ℝ 2 ≤ 2)
  unfold Matrix.PosSemidef
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa [FunctionalInequalities.Probability.Stein.hessianMatrix, bilinearIteratedFDerivTwo] using
      hs (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
  · intro z
    let v : EuclideanSpace ℝ (Fin n) :=
      z.sum (fun i zi => zi • EuclideanSpace.basisFun (Fin n) ℝ i)
    have hv := FunctionalInequalities.Analysis.directional_second_deriv_nonneg_readable hconv hψ hcontact htouch v
    have hquad :
        z.sum (fun i zi =>
            z.sum (fun j zj =>
              star zi * FunctionalInequalities.Probability.Stein.hessianMatrix ψ x₀ i j * zj)) =
          bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
      simp [v, FunctionalInequalities.Probability.Stein.hessianMatrix, bilinearIteratedFDerivTwo, Finsupp.sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hs (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)]
      ring
    rw [hquad]
    exact hv
