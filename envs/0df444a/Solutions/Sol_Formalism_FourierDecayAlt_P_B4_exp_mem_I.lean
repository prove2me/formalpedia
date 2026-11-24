-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.exp_mem_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:39.404424+00:00
-- url     : https://prove2.me/submissions/a818f640-bd06-47a7-bef3-34509ac903ce

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
theorem _root_.solution {σ : ℝ} (h : |σ| ≤ Real.log 2) : Real.exp σ ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  rw [abs_le] at h
  rw [Set.mem_Icc]
  constructor
  · have := Real.exp_le_exp.mpr h.1
    rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at this
  · have := Real.exp_le_exp.mpr h.2
    rwa [Real.exp_log (by norm_num)] at this
end Formalism.FourierDecayAlt.P.B4
