-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.lie_element_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:58.856462+00:00
-- url     : https://prove2.me/submissions/2ba92ac0-75e7-46fd-87b4-4f88abba67e3

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_lie_element_eq_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hermitian_entry_zero_or_weights_cancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_diagonal_lie_element_self_adjoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_diagonal_entry_dilation_generator_le_one

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
theorem _root_.solution (k r : ℕ) : unitLie k r (X0 k r) := by
  constructor
  · unfold inLie
    rw [lie_element_eq_diagonal, Matrix.diagonal_conjTranspose]
    ext i j
    rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply, Pi.star_apply, diagonal_lie_element_self_adjoint]
    rcases hermitian_entry_zero_or_weights_cancel k r i j with h | h
    · rw [h]; ring
    · linear_combination (Hpk k r i j) * h
  · intro i j
    rw [lie_element_eq_diagonal, Matrix.diagonal_apply]
    split_ifs with h
    · exact norm_diagonal_entry_dilation_generator_le_one k r i
    · simp
end Formalism.FourierDecayAlt.P.B6
