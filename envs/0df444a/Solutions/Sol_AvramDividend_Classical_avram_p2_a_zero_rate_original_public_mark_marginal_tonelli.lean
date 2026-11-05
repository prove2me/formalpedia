-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_public_mark_marginal_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:42:06.453087+00:00
-- url     : https://prove2.me/submissions/90e0cdd0-145f-4e63-8ad3-1a30a9212f93

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_public_original_mark_marginal_tonelli
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-original finite-horizon mark marginal from the Proved independent
    Tonelli bridge, with the exact indicator/restriction integrals identified. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ markRate : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        markRate B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∫⁻ y, g y ∂markRate) =
        (∫⁻ ω, ∫⁻ p : ℝ≥0 × ℝ,
          (if p.1 ∈ Ioc (0 : ℝ≥0) T then g p.2 else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by
  obtain ⟨ρ, hρ, hρtest⟩ :=
    avram_p2_a_assist_public_original_mark_marginal_tonelli X T g hg
  refine ⟨ρ, hρ, ?_⟩
  have hA : MeasurableSet
      (Ioc (0 : ℝ≥0) T ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  calc
    (∫⁻ y, g y ∂ρ) =
      (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (Set.univ : Set ℝ)),
        g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := hρtest
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      rw [← lintegral_indicator hA]
      apply lintegral_congr_ae
      filter_upwards [] with p
      simp [Set.indicator, Set.mem_prod]
