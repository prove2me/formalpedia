-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_rightcont_source_predictable_total_occupation_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:49:31.202687+00:00
-- url     : https://prove2.me/submissions/fd57cf64-5d5b-41c9-8a67-c69a615647f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_adapted_rectangle_eq_intrinsic_count_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Same original BV occupation, lifted through its identical rightCont paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K) :
    M (((Ioc 0 T) ×ˢ (Set.univ : Set Ω)) ×ˢ (Set.univ : Set ℝ)) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  obtain ⟨Y, hYX, _hc, _hσ, _hν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hKY : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ Y.X u ω -
            Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, Y.X u ω -
            Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u))) := by
    intro ω
    simpa only [hYX] using hK ω
  have hOcc :=
    avram_wave5_01_actual_source_predictable_adapted_rectangle_eq_intrinsic_count_lintegral
      Y K hKY M hM 0 T Set.univ MeasurableSet.univ
      Set.univ MeasurableSet.univ
  rw [hOcc]
  simpa only [hYX, Measure.restrict_univ] using
    (avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
      X hBV hFinite T hT grid hGrid hMesh hBound)
