-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.scaled_decay_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:47.175851+00:00
-- url     : https://prove2.me/submissions/67f0407e-6ef6-4ab6-9533-486445a836cb

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rpow_neg_two_eq_inv_sq

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
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {t : ℝ} (ht : 1 / 2 ≤ t) (x : ℝ) :
    (1 + |t * x|) ^ (-2 : ℝ) ≤ 4 * (1 + |x|) ^ (-2 : ℝ) := by
  rw [rpow_neg_two_eq_inv_sq (by positivity), rpow_neg_two_eq_inv_sq (by positivity)]
  have h0 : 0 ≤ |x| := abs_nonneg x
  have h1 : |t * x| = t * |x| := by rw [abs_mul, abs_of_nonneg (by linarith)]
  rw [h1, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 1 + |x| ≤ 2 * (1 + t * |x|) := by nlinarith
  have h3 : 0 ≤ 1 + |x| := by positivity
  nlinarith
end Formalism.FourierDecayAlt.P.B6
