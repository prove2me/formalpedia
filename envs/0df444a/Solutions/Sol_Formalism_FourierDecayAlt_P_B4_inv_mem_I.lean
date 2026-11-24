-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.inv_mem_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:27:45.004684+00:00
-- url     : https://prove2.me/submissions/6bef488e-aafc-41ac-ae2c-5f8726610b17

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
theorem _root_.solution {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : t⁻¹ ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  have hs : t⁻¹ * t = 1 := inv_mul_cancel₀ hpos.ne'
  have hsp : 0 < t⁻¹ := inv_pos.mpr hpos
  rw [Set.mem_Icc]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h2 hsp.le]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hsp.le]
end Formalism.FourierDecayAlt.P.B4
