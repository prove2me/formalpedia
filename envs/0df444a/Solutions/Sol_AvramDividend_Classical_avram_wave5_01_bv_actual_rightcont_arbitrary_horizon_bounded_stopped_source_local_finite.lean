-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_rightcont_arbitrary_horizon_bounded_stopped_source_local_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:39:37.33371+00:00
-- url     : https://prove2.me/submissions/e4fc32a7-7964-4ed6-90e7-0bef777a2a16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_original_rightcont_horizon_stopped_source_local_finite_all_marks
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Arbitrary original stopped-source regions inherit finite occupation mass
from the proved full finite-horizon original-source bound. -/
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
    (hST : S ⊆ {p | p.1.1 ≤ T})
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) ≠ ⊤ := by
  classical
  let E : Set ((ℝ≥0 × Ω) × ℝ) :=
    (Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B
  let H : Set ((ℝ≥0 × Ω) × ℝ) :=
    {p | p.1.1 ≤ T}
  have hE : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] E :=
    MeasurableSet.univ.prod hB
  have hLocal : (M.restrict H) E ≠ ⊤ := by
    simpa only [E] using
      (avram_wave5_01_bv_actual_original_rightcont_horizon_stopped_source_local_finite_all_marks
        X hBV hFinite T hT grid hGrid hMesh hBound K hK M hM
        H rfl (M.restrict H) rfl B hB)
  have hSub : E ∩ S ⊆ E ∩ H := by
    intro p hp
    exact ⟨hp.1, hST hp.2⟩
  have hUpper : MT E ≤ (M.restrict H) E := by
    calc
      MT E = M (E ∩ S) := by
        rw [hMT, Measure.restrict_apply hE]
      _ ≤ M (E ∩ H) := measure_mono hSub
      _ = (M.restrict H) E := (Measure.restrict_apply hE).symm
  exact (lt_of_le_of_lt hUpper (lt_top_iff_ne_top.mpr hLocal)).ne
