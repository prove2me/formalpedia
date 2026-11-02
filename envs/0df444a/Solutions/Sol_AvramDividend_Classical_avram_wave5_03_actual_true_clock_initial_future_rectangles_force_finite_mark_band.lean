-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:28:41.680424+00:00
-- url     : https://prove2.me/submissions/da94ac5e-ff22-4526-905a-bffe664361b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_any_true_predictable_clock_original_initial_source_compensator_rectangle
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True source initial and future compensation controls total finite mark bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
    (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) (M : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))) (hM : M = P.bind K)
    (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ)) (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))) (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) (hμfinite : μ Set.univ < ∞) (hμclock : ∀ A : Set (ℝ≥0 × Ω),
    MeasurableSet[𝓕.rightCont.predictable] A → μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBfinite : (X.ν.restrict (Iio (0 : ℝ))) B < ∞) (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ), MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
    MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C')) : MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) ≠ ∞ := by
  classical
  let A0 : Set ((ℝ≥0 × Ω) × ℝ) :=
    (({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) ×ˢ B)
  let A1 : Set ((ℝ≥0 × Ω) × ℝ) :=
    ((Set.Ioi (0 : ℝ≥0) ×ˢ (Set.univ : Set Ω)) ×ˢ B)
  let AT : Set ((ℝ≥0 × Ω) × ℝ) :=
    (Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B
  have hcover : AT = A0 ∪ A1 := by
    ext p
    rcases p with ⟨⟨t, ω⟩, z⟩
    have ht : t = 0 ∨ 0 < t := by
      rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    simp only [AT, A0, A1, Set.mem_prod, Set.mem_univ,
      Set.mem_singleton_iff, Set.mem_Ioi, true_and, Set.mem_union]
    constructor
    · intro hz
      rcases ht with h0 | hpos
      · exact Or.inl ⟨⟨h0, trivial⟩, hz⟩
      · exact Or.inr ⟨⟨hpos, trivial⟩, hz⟩
    · rintro (⟨_, hz⟩ | ⟨_, hz⟩)
      · exact hz
      · exact hz
  have hsub0 : A0 ⊆ AT := by
    intro p hp
    exact ⟨Set.mem_univ _, hp.2⟩
  have hsub1 : A1 ⊆ AT := by
    intro p hp
    exact ⟨Set.mem_univ _, hp.2⟩
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : SigmaFinite X.ν :=
    avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields X
  have hNfinite : N AT < ∞ := by
    rw [hN]
    change (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) (Set.univ ×ˢ B) < ∞
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top hμfinite hBfinite
  have hA0eq : MT A0 = N A0 := by
    change MT (({(0 : ℝ≥0)} ×ˢ Set.univ) ×ˢ B) =
      N (({(0 : ℝ≥0)} ×ˢ Set.univ) ×ˢ B)
    rw [hN]
    exact
      avram_wave5_03_any_true_predictable_clock_original_initial_source_compensator_rectangle
        X K hK M hM S MT hMT T μ hμclock
        Set.univ MeasurableSet.univ B hB
  have hA1eq : MT A1 = N A1 :=
    hFuture 0 Set.univ B MeasurableSet.univ hB
  have hMT0finite : MT A0 < ∞ := by
    rw [hA0eq]
    exact lt_of_le_of_lt (measure_mono hsub0) hNfinite
  have hMT1finite : MT A1 < ∞ := by
    rw [hA1eq]
    exact lt_of_le_of_lt (measure_mono hsub1) hNfinite
  have hMTfinite : MT AT < ∞ := by
    calc
      MT AT = MT (A0 ∪ A1) := by rw [hcover]
      _ ≤ MT A0 + MT A1 := measure_union_le _ _
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hMT0finite, hMT1finite⟩
  exact ne_of_lt hMTfinite