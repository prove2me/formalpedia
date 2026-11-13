-- Prove2me | solution 2 for AvramDividend.Classical.avram_gbB100_original_gaussian_fixed_level_occupation_null
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:10:13.448597+00:00
-- url     : https://prove2.me/submissions/5b52a3cd-4ce4-4321-92d0-00eea712202c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
import Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_gbB200_martingale_FV_fixed_level_null_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Fixed-level occupation of the original postpayment reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = b} = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hσ : 0 < X.σ :=
    avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
      X hBV hν
  obtain ⟨hM, hQ, hFV, hCont, hAlg⟩ :=
    avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
      X hν x D hD
  exact avram_gbB200_martingale_FV_fixed_level_null_occupation
    (𝓕 := 𝓕.rightCont) X.X X.c X.σ hσ hM hQ hCont
    (fun t ω => rightLimit D t ω) hFV x b n ρ

