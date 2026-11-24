-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.aDil_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:06:03.477881+00:00
-- url     : https://prove2.me/submissions/bae18952-51f2-4e56-9f0e-0ba3c3daa123

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  apply Matrix.inv_eq_left_inv
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs
  · push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ htc)]
  · simp
  · push_cast
    rw [inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ htc)]
end Formalism.FourierDecayAlt.P.B5
