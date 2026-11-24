-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.exp_dilation_generator_eq_aDil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:40:22.102568+00:00
-- url     : https://prove2.me/submissions/fe6c418e-d5c1-4ce6-9e35-eddb27a771c8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rr_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_lie_element_eq_diagonal

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (k r : ℕ) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X0 k r) = aDil k r (Real.exp (s / rr r)) := by
  rw [lie_element_eq_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  unfold aDil
  congr 1
  funext i
  rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  have hr : (rr r) ≠ 0 := (rr_pos r).ne'
  unfold dilationGeneratorDiagonal
  split_ifs with h1 h2
  · rw [← Real.exp_nat_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    unfold rr; field_simp
  · simp
  · rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    unfold rr; field_simp
end Formalism.FourierDecayAlt.P.B6
