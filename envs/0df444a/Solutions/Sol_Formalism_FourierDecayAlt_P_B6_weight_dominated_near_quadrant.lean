-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.weight_dominated_near_quadrant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:14.786927+00:00
-- url     : https://prove2.me/submissions/499966e5-193b-4eba-a081-fb17adda8f6f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_LL_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_wt_le

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {τ₀ : ℝ × ℝ} (h₀ : τ₀ ∈ Quad) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ × ℝ, τ₀.1 / 2 < τ.1 → τ₀.2 / 2 < τ.2 → ∀ p, wt D τ p ≤ M * LL D p := by
  have a1 : 0 < τ₀.1 := h₀.1
  have a2 : 0 < τ₀.2 := h₀.2
  refine ⟨4 * max 1 ((τ₀.1 / 2) ^ 2)⁻¹ * max 1 ((τ₀.2 / 2) ^ 2)⁻¹, by positivity, ?_⟩
  intro τ h1 h2 p
  have b1 : 0 < τ.1 := lt_trans (by positivity) h1
  have b2 : 0 < τ.2 := lt_trans (by positivity) h2
  refine (wt_le D b1 b2 p).trans ?_
  have c1 : max 1 (τ.1 ^ 2)⁻¹ ≤ max 1 ((τ₀.1 / 2) ^ 2)⁻¹ := by
    apply max_le_max le_rfl
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) h1.le 2
  have c2 : max 1 (τ.2 ^ 2)⁻¹ ≤ max 1 ((τ₀.2 / 2) ^ 2)⁻¹ := by
    apply max_le_max le_rfl
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) h2.le 2
  have hL := LL_nonneg D p
  gcongr
end Formalism.FourierDecayAlt.P.B6
