-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_quad_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:16.976804+00:00
-- url     : https://prove2.me/submissions/9e57de1f-df77-485c-92ba-ea18b819ad30

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {r Γ : ℝ} (hr : 0 < r) (h0 : ‖φ 0‖ ≤ Γ)
    (h2 : ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ Γ) (i : ℕ) {x : E} (hx : x ∈ Metric.closedBall (0 : E) r) :
    ‖iteratedFDeriv ℝ i (quad φ) x‖ ≤ Γ * (r + 1) ^ 2 := by
  have hxr : ‖x‖ ≤ r := by simpa using hx
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans h0
  cases i with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have h1 : ‖fderiv ℝ (fderiv ℝ φ) 0 x x‖ ≤ Γ * r * r := by
      refine ((fderiv ℝ (fderiv ℝ φ) 0 x).le_opNorm x).trans ?_
      refine mul_le_mul (((fderiv ℝ (fderiv ℝ φ) 0).le_opNorm x).trans ?_) hxr (norm_nonneg _) (by positivity)
      exact mul_le_mul h2 hxr (norm_nonneg _) hΓ
    have h3 : ‖quad φ x‖ ≤ ‖φ 0‖ + 1 / 2 * ‖fderiv ℝ (fderiv ℝ φ) 0 x x‖ := by
      unfold quad
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      norm_num
    nlinarith [mul_nonneg hΓ hr.le, mul_nonneg (mul_nonneg hΓ hr.le) hr.le]
  | succ i =>
    rw [← norm_iteratedFDeriv_fderiv, E_quad_fderiv hφ]
    have h := (Sym.clm (A := Set.univ) (N := i) (fderiv ℝ (fderiv ℝ φ) 0) (σ := 1) one_pos).2 x trivial i le_rfl
    refine h.trans ?_
    have hw1 : (1 : ℝ) ≤ wt 1 x := by unfold wt; linarith [norm_nonneg x]
    have hw2 : wt 1 x ≤ r + 1 := by unfold wt; linarith
    have hz : wt 1 x ^ ((1 : ℤ) - (i : ℤ)) ≤ r + 1 := by
      cases i with
      | zero => simpa using hw2
      | succ j =>
        refine (zpow_le_one_of_nonpos₀ hw1 (by push_cast; omega)).trans (by linarith)
    have hz0 : 0 ≤ wt 1 x ^ ((1 : ℤ) - (i : ℤ)) := zpow_nonneg (by linarith) _
    calc ‖fderiv ℝ (fderiv ℝ φ) 0‖ * wt 1 x ^ ((1 : ℤ) - (i : ℤ)) ≤ Γ * (r + 1) :=
          mul_le_mul h2 hz hz0 hΓ
      _ ≤ Γ * (r + 1) ^ 2 := by nlinarith [mul_nonneg hΓ hr.le]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
