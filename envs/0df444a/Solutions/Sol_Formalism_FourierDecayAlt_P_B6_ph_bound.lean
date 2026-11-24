-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.ph_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:40.953314+00:00
-- url     : https://prove2.me/submissions/4a6dfdd7-1f16-4492-a33a-98c4a59f0e3c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inSS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_translated_product_integrable_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_integrand_bound

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
theorem _root_.solution (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    admitted α cA A → admitted α cB B → ∀ p, D.inSS p → ‖Ph D A B p‖ ≤ K * cA * cB * XX Ξ p := by
  obtain ⟨K, hK0, hK⟩ := translated_product_integrable_bound H
  refine ⟨(Module.finrank ℂ Wq : ℝ) * K, by positivity, fun A B cA cB hA hB p hp => ?_⟩
  have hxy := inSS_mem D hp
  have h := hK A B cA cB hA hB _ hxy.1 _ hxy.2
  unfold Ph
  refine (norm_integral_le_of_norm_le (h.1.const_mul (Module.finrank ℂ Wq : ℝ))
    (Eventually.of_forall fun g => hilbert_schmidt_integrand_bound D A B hp _)).trans ?_
  rw [integral_const_mul]
  calc (Module.finrank ℂ Wq : ℝ) * _ ≤ (Module.finrank ℂ Wq : ℝ) * (K * cA * cB * XX Ξ p) :=
        mul_le_mul_of_nonneg_left h.2 (by positivity)
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.B6
