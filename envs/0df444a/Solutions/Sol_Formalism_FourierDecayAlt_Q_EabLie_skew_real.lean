-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.skew_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:27.404808+00:00
-- url     : https://prove2.me/submissions/f32abf52-c15e-4d20-b0a3-1171b67fa1da

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r)) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -(Hpk k r * ((t : ℂ) • X) * Hpk k r) := by
  rw [Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal]
  simp [Matrix.smul_mul, Matrix.mul_smul]
end Formalism.FourierDecayAlt.Q.EabLie
