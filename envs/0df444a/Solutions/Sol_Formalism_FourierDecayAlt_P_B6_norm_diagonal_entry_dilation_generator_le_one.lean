-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.norm_diagonal_entry_dilation_generator_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:27:51.339841+00:00
-- url     : https://prove2.me/submissions/6077e1c7-cbe4-42af-b94c-2c73fe7aa071

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : ‖dilationGeneratorDiagonal k r i‖ ≤ 1 := by
  unfold dilationGeneratorDiagonal
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  split_ifs with h1 h2
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one hr]
    have : ((r - i.val : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le _ _
    linarith
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), div_le_one hr]
    have h3 : i.val - (r + k) ≤ r := by have := i.isLt; omega
    have : ((i.val - (r + k) : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h3
    linarith
end Formalism.FourierDecayAlt.P.B6
