-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.abs_log_le_log_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:35.080403+00:00
-- url     : https://prove2.me/submissions/1802ec1f-ab54-47fc-bc91-116b01ebc94a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : |Real.log t| ≤ Real.log 2 := by
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  rw [abs_le]
  constructor
  · have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h1
    rw [one_div, Real.log_inv] at this
    linarith
  · exact Real.log_le_log hpos h2
end Formalism.FourierDecayAlt.P.B4
