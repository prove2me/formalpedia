-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.admissible_two_sided_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:09:24.904556+00:00
-- url     : https://prove2.me/submissions/5c2a3ea2-450c-4822-b425-a73745291e50

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_mul_le
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {f : Mat k r → E}
    (hα : 0 ≤ α) (hf : admitted α c f) {u v : Mat k r} (hu : u ∈ GV k r) (hv : v ∈ GV k r) :
    admitted α (c * (gN u⁻¹ * gN v⁻¹) ^ α) (fun g => f (u * g * v)) := by
  have hmaps : ∀ g ∈ GV k r, u * g * v ∈ GV k r := fun g hg => WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hu hg) hv
  refine ⟨?_, ?_⟩
  · have hc : Continuous fun g : Mat k r => u * g * v :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hf.1.comp hc.continuousOn hmaps
  · intro g hg
    have hw := hmaps g hg
    have huu := WeylGroupFacts.isUnit_of_uh hu
    have hvu := WeylGroupFacts.isUnit_of_uh hv
    have eg : g = u⁻¹ * (u * g * v) * v⁻¹ := by
      rw [Matrix.mul_assoc u g v, Matrix.nonsing_inv_mul_cancel_left _ _ huu, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hvu, Matrix.mul_one]
    have h1 : gN g ≤ (gN u⁻¹ * gN v⁻¹) * gN (u * g * v) := by
      calc gN g = gN (u⁻¹ * (u * g * v) * v⁻¹) := by rw [← eg]
        _ ≤ gN (u⁻¹ * (u * g * v)) * gN v⁻¹ := gN_mul_le _ _
        _ ≤ gN u⁻¹ * gN (u * g * v) * gN v⁻¹ :=
            mul_le_mul_of_nonneg_right (gN_mul_le _ _) (gN_nonneg _)
        _ = (gN u⁻¹ * gN v⁻¹) * gN (u * g * v) := by ring
    have hK : 0 ≤ gN u⁻¹ * gN v⁻¹ := mul_nonneg (gN_nonneg _) (gN_nonneg _)
    have h2 : gN g ^ α ≤ (gN u⁻¹ * gN v⁻¹) ^ α * gN (u * g * v) ^ α := by
      rw [← Real.mul_rpow hK (gN_nonneg _)]
      exact Real.rpow_le_rpow (gN_nonneg _) h1 hα
    calc gN g ^ α * ‖f (u * g * v)‖
        ≤ ((gN u⁻¹ * gN v⁻¹) ^ α * gN (u * g * v) ^ α) * ‖f (u * g * v)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = (gN u⁻¹ * gN v⁻¹) ^ α * (gN (u * g * v) ^ α * ‖f (u * g * v)‖) := by ring
      _ ≤ (gN u⁻¹ * gN v⁻¹) ^ α * c :=
          mul_le_mul_of_nonneg_left (hf.2 _ hw) (Real.rpow_nonneg hK _)
      _ = c * (gN u⁻¹ * gN v⁻¹) ^ α := by ring
end Formalism.FourierDecayAlt.P.B6
