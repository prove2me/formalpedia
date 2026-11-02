-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_original_rightcont_horizon_stopped_source_local_finite_all_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:49:39.976948+00:00
-- url     : https://prove2.me/submissions/82800993-7c04-41d3-9f48-d342b0118ea0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Finite-activity BV actual stopped original jump occupation localises
on every Borel band, without a marked-Poisson replacement. -/
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
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) ≠ ⊤ := by
  classical
  let E : Set ((ℝ≥0 × Ω) × ℝ) :=
    (Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B
  let Epos : Set ((ℝ≥0 × Ω) × ℝ) :=
    (((Ioc 0 T) ×ˢ (Set.univ : Set Ω)) ×ˢ B)
  let Ezero : Set ((ℝ≥0 × Ω) × ℝ) :=
    (({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) ×ˢ B)
  have hE : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] E :=
    MeasurableSet.univ.prod hB
  have hPos : M Epos < ⊤ := by
    have hOcc :=
      avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
        X K hK M hM 0 T Set.univ MeasurableSet.univ B hB
    have hFiniteBand :=
      avram_wave5_01_bv_actual_intrinsic_borel_mark_band_expected_count_le_finite_total_rate
        X hBV hFinite T hT grid hGrid hMesh hBound B hB
    rw [hOcc]
    simpa only [Measure.restrict_univ] using hFiniteBand.2
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
  have hZero : M Ezero = 0 :=
    avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
      Y K hKY M hM Set.univ MeasurableSet.univ
      B hB
  have hSub : E ∩ S ⊆ Epos ∪ Ezero := by
    intro p hp
    have ht : p.1.1 ≤ T := by
      simpa only [hST, Set.mem_setOf_eq] using hp.2
    have hmark : p.2 ∈ B := hp.1.2
    by_cases hz : p.1.1 = 0
    · right
      simp [Ezero, Set.mem_prod, hz, hmark]
    · left
      have hpositive : (0 : ℝ≥0) < p.1.1 :=
        pos_iff_ne_zero.mpr hz
      simp [Epos, Set.mem_prod, hpositive, ht, hmark]
  have hUpper : MT E ≤ M Epos := by
    calc
      MT E = M (E ∩ S) := by
        rw [hMT, Measure.restrict_apply hE]
      _ ≤ M (Epos ∪ Ezero) := measure_mono hSub
      _ ≤ M Epos + M Ezero := measure_union_le Epos Ezero
      _ = M Epos := by rw [hZero, add_zero]
  exact (lt_of_le_of_lt hUpper hPos).ne
