-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.cc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:28:57.226735+00:00
-- url     : https://prove2.me/submissions/6c5d524d-e594-439e-8477-d1c6db8209cf

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
theorem _root_.solution {F : Mat k r → E} {A c : ℝ} {m : ℕ} (h : CCle A m F c) : 0 ≤ c := by
  unfold CCle at h
  have h1 : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have := h.2 [] [] (by simp) (by simp) (by simp) 1 h1
  exact le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) A) (norm_nonneg _)) this
end Formalism.FourierDecayAlt.P.B4
