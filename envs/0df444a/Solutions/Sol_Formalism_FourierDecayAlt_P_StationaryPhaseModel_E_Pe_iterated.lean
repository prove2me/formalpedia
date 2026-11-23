-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_Pe_iterated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:02.059993+00:00
-- url     : https://prove2.me/submissions/32343ca0-b263-4dc1-ba06-9effb4b79197

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_iteratedFDeriv_comp_neg

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
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) {i : ℕ} (hi : i ≤ n) (x : E) :
    iteratedFDeriv ℝ i (E_Pe φ) x =
      (1 / 2 : ℝ) • (iteratedFDeriv ℝ i (E_P φ) x + (-1 : ℝ) ^ i • iteratedFDeriv ℝ i (E_P φ) (-x)) := by
  have hin : ((i : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  have hP : ContDiff ℝ i (E_P φ) := (E_P_contDiff hφ).of_le hin
  have he : E_Pe φ = (1 / 2 : ℝ) • (E_P φ + fun y => E_P φ (-y)) := by
    funext y
    simp [E_Pe]
  have hPn : ContDiff ℝ i (fun y => E_P φ (-y)) := hP.comp contDiff_neg
  have hadd : ContDiff ℝ i (E_P φ + fun y => E_P φ (-y)) := hP.add hPn
  rw [he, iteratedFDeriv_const_smul_apply hadd.contDiffAt,
    iteratedFDeriv_add_apply hP.contDiffAt hPn.contDiffAt,
    E_iteratedFDeriv_comp_neg hP le_rfl]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
