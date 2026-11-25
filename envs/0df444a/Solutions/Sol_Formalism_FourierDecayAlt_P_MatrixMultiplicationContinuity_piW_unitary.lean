-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:46.760254+00:00
-- url     : https://prove2.me/submissions/df7490a4-5f74-4396-bb43-8ac3989679d1

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_piW_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ w, ‖π h w‖ = ‖w‖ := by
  exact (piW_facts hT hπ).2.2.1
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
