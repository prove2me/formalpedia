-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:16.918546+00:00
-- url     : https://prove2.me/submissions/97794780-1a94-4f15-a43d-d06f2be189da

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_fderiv

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
theorem _root_.solution {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : fderiv ℝ φ 0 = 0) :
    ∀ i : ℕ, i < 3 → iteratedFDeriv ℝ i (E_P φ) 0 = 0 := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (E_P φ)) 0 = 0 := by
    rw [E_P_fderiv hφ]
    have := ((hd 0).hasFDerivAt.sub (fderiv ℝ (fderiv ℝ φ) 0).hasFDerivAt).fderiv
    rw [sub_self] at this
    exact this
  intro i hi
  rw [← norm_eq_zero]
  interval_cases i
  · rw [norm_iteratedFDeriv_zero]
    simp [E_P, quad]
  · rw [norm_iteratedFDeriv_one, E_P_fderiv hφ]
    simp [hc]
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, h2, norm_zero]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
