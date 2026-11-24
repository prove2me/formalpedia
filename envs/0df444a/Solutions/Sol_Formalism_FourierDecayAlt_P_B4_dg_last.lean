-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dg_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:37.441571+00:00
-- url     : https://prove2.me/submissions/671a0797-b860-49ad-98e2-25d5d7e2c7ea

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
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (k r : ℕ) (t : ℝ) (a : Fin r) (h : ¬ a.val + 1 < r) :
    dg k r t (eI k r a) = (t : ℂ) := by
  have e : r - a.val = 1 := by have := a.isLt; omega
  simp only [dg, eI, Fin.is_lt, ↓reduceIte, e, pow_one]
end Formalism.FourierDecayAlt.P.B4
