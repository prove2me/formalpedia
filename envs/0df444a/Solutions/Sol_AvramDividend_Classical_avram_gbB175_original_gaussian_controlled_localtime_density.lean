-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB175_original_gaussian_controlled_localtime_density
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:26:10.892289+00:00
-- url     : https://prove2.me/submissions/51d15a43-d01f-4c8c-be0e-33ebb9ae7cb2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
import Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
import Theorems.Thm_AvramDividend_Classical_avram_gbB241_locally_bounded_compact_support_density_uniform
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original zero-jump Gaussian local time density derived from semimartingale B243. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0),
      (∀ z : ℝ, ℓ z ≤ (B : ℝ≥0∞)) ∧
      ∀ (y ε : ℝ), 0 < ε → ε ≤ 1 →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - y) < ε} ≤
        ∫⁻ z in Ioo (y - ε) (y + ε), ℓ z ∂volume := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hσ : 0 < X.σ :=
    avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
      X hBV hν
  obtain ⟨hM, hQ, hFV, hCont, hAlg⟩ :=
    avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
      X hν x D hD
  have hRep :=
    avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
      (𝓕 := 𝓕.rightCont) X.X X.c X.σ hσ hM hQ hCont
      (fun t ω => rightLimit D t ω) hFV x n ρ
  filter_upwards [hRep] with ω hω
  obtain ⟨R, ℓ, hNonneg, hSupport, hLocal, hOccupation⟩ := hω
  obtain ⟨B, hB0, hBound⟩ :=
    avram_gbB241_locally_bounded_compact_support_density_uniform
      ℓ R hLocal hNonneg hSupport
  refine ⟨(fun z => ENNReal.ofReal (ℓ z)), Real.toNNReal B, ?_, ?_⟩
  · intro z
    exact ENNReal.ofReal_le_ofReal (hBound z)
  · intro y ε hε hε1
    have hBand : {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - y) < ε} =
        {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω ∈ Ioo (y-ε) (y+ε)} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨ht0, htn, htρ, ht⟩
        have ha := abs_lt.mp ht
        refine ⟨ht0, htn, htρ, ?_⟩
        constructor <;> linarith
      · rintro ⟨ht0, htn, htρ, ht⟩
        refine ⟨ht0, htn, htρ, abs_lt.mpr ?_⟩
        constructor <;> linarith [ht.1, ht.2]
    rw [hBand]
    exact le_of_eq (hOccupation (y-ε) (y+ε))
