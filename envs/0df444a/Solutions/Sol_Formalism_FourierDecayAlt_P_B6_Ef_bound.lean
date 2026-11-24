-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Ef_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:47.414655+00:00
-- url     : https://prove2.me/submissions/efedd25b-0dd0-4f85-a2af-14cca0a7ee60

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Wd_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Wd_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_XX_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_QR_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Ef_zero

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
theorem _root_.solution (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
    AdmW α c 2 2 F → AdmW α c' 2 2 F' → ∀ p, D.inSS p → ∀ t, ‖Ef D F F' p t‖ ≤ K * c * c' * XX Ξ p := by
  obtain ⟨K, hK, hb⟩ := QR_bound H
  obtain ⟨Γ, hΓ, hg⟩ := gam_bound (Wd_contDiff D) (Wd_tsupport D) (rr r)
  refine ⟨9 * (Γ * Γ * (16 * K)), by positivity, ?_⟩
  intro F F' c c' hF hF' p hp t
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hX := XX_nonneg Ξ p
  have nn : 0 ≤ K * c * c' * XX Ξ p := by positivity
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · unfold Ef
    have term : ∀ m ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
        ‖((gam (rr r) (Wd D) m t.1 * gam (rr r) (Wd D) l t.2 : ℝ) : ℂ) * QR D p m l F F' t.1 t.2‖ ≤
          Γ * Γ * (16 * (K * c * c' * XX Ξ p)) := by
      intro m hm l hl
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hm' : m ≤ 2 := by have := Finset.mem_range.1 hm; omega
      have hl' : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
      have q := hb m l F F' c c' (admissibleWeight_mono hF hl' hm') (admissibleWeight_mono hF' hl' hm') p hp t.1
        ⟨ht.1.1.le, ht.1.2.le⟩ t.2 ⟨ht.2.1.le, ht.2.2.le⟩
      have p2 : (2 : ℝ) ^ (m + l) ≤ 16 := by
        calc (2 : ℝ) ^ (m + l) ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 16 := by norm_num
      calc _ ≤ (Γ * Γ) * (2 ^ (m + l) * (K * c * c' * XX Ξ p)) :=
            mul_le_mul (mul_le_mul (hg m _) (hg l _) (abs_nonneg _) hΓ) q (norm_nonneg _) (by positivity)
        _ ≤ _ := by gcongr
    calc _ ≤ ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3, Γ * Γ * (16 * (K * c * c' * XX Ξ p)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => term m hm l hl))
      _ = _ := by simp; ring
  · rw [Ef_zero D F F' p ht, norm_zero]; positivity
end Formalism.FourierDecayAlt.P.B6
