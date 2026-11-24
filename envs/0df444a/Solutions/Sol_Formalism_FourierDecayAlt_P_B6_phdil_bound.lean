-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.phdil_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:53.068819+00:00
-- url     : https://prove2.me/submissions/eaf1e758-4375-42ec-8b69-57c183e8c5cd

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_gN_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_two_sided_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


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
    admitted α cA A → admitted α cB B → ∀ p, D.inSS p → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, ∀ y ∈ Set.Icc (1 / 2 : ℝ) 2,
      ‖Ph D A B (dilation₂ (x, y) p)‖ ≤ K * cA * cB * XX Ξ p := by
  obtain ⟨K, hK0, hK⟩ := ph_bound H
  obtain ⟨M, hM0, hM⟩ := aDil_gN_bound k r (a := 1 / 2) (b := 2) (by norm_num)
  refine ⟨K * ((M * M) ^ α * (M * M) ^ α), by positivity, fun A B cA cB hA hB p hp x hx y hy => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have hax := aDil_mem k r hx0
  have hay := aDil_inv_mem k r hy0
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  rw [ph_dil H A B hp hx0 hy0]
  have h := hK _ _ _ _ (admissible_two_sided_translate H.α_nonneg hA hax hay) (admissible_two_sided_translate H.α_nonneg hB hax hay) p hp
  refine h.trans ?_
  have hXX : 0 ≤ XX Ξ p := by unfold XX; positivity
  have he : (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α ≤ (M * M) ^ α := by
    rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh (aDil_mem k r hy0))]
    exact Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _))
      (mul_le_mul (hM x hx).2 (hM y hy).1 (gN_nonneg _) hM0) H.α_nonneg
  have he0 : 0 ≤ (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α :=
    Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _
  calc K * (cA * (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α) *
        (cB * (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α) * XX Ξ p
      ≤ K * (cA * (M * M) ^ α) * (cB * (M * M) ^ α) * XX Ξ p := by gcongr
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.B6
