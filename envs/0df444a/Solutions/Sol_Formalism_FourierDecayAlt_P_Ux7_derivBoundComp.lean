-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux7.derivBoundComp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:10.676265+00:00
-- url     : https://prove2.me/submissions/646fa30f-1d9d-4478-afa6-6e653b7a9180

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux7
namespace Formalism.FourierDecayAlt.P.Ux7
theorem _root_.solution : DerivBoundComp := by
  intro s k V V' _ _ _ _ T Φ Kd bd h Z hZ
  obtain ⟨hc, hb⟩ := h Z hZ
  have hc' : ContDiffAt ℝ k (fun Z => T (Φ Z)) Z :=
    (T.restrictScalars ℝ).contDiff.contDiffAt.comp Z hc
  refine ⟨hc', fun j hj => ?_⟩
  have k1 : ‖iteratedFDeriv ℝ j (fun y => (T.restrictScalars ℝ) (Φ y)) Z‖ ≤
      ‖T.restrictScalars ℝ‖ * ‖iteratedFDeriv ℝ j Φ Z‖ :=
    (T.restrictScalars ℝ).norm_iteratedFDeriv_comp_left hc (by exact_mod_cast hj)
  rw [ContinuousLinearMap.norm_restrictScalars] at k1
  show _ ≤ ‖T‖ * bd Z
  exact k1.trans (mul_le_mul_of_nonneg_left (hb j hj) (norm_nonneg _))
end Formalism.FourierDecayAlt.P.Ux7
