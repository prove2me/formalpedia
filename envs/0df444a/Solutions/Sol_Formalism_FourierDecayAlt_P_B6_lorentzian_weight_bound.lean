-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.lorentzian_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:43.613532+00:00
-- url     : https://prove2.me/submissions/0364eaa9-5dba-4b28-b660-cea317cdce4d

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {τ : ℝ} (h : 0 < τ) (l : ℝ) :
    (1 + τ ^ 2 * l ^ 2)⁻¹ ≤ 2 * max 1 (τ ^ 2)⁻¹ * (1 + |l|) ^ (-2 : ℝ) := by
  have e : (1 + |l|) ^ (-2 : ℝ) = ((1 + |l|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_num
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  have m1 : (1 : ℝ) ≤ max 1 (τ ^ 2)⁻¹ := le_max_left _ _
  have m2 : (τ ^ 2)⁻¹ ≤ max 1 (τ ^ 2)⁻¹ := le_max_right _ _
  have m3 : 1 ≤ max 1 (τ ^ 2)⁻¹ * τ ^ 2 := by
    have : (τ ^ 2)⁻¹ * τ ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    calc (1 : ℝ) = (τ ^ 2)⁻¹ * τ ^ 2 := this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right m2 (by positivity)
  have hl : l ^ 2 = |l| ^ 2 := (sq_abs l).symm
  rw [hl]
  set a := |l| with ha
  have ha0 : 0 ≤ a := abs_nonneg l
  set M := max 1 (τ ^ 2)⁻¹
  have : (1 + τ ^ 2 * a ^ 2) * (2 * M) = 2 * M + 2 * (M * τ ^ 2) * a ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg (1 - a), mul_le_mul_of_nonneg_right m3 (sq_nonneg a)]
end Formalism.FourierDecayAlt.P.B6
