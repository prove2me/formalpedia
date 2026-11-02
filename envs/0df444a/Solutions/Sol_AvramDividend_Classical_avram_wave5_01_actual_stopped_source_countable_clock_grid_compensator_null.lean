-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_stopped_source_countable_clock_grid_compensator_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:53:49.109978+00:00
-- url     : https://prove2.me/submissions/97de0bcc-a3bd-45ea-a95d-6407410e2654

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_stopped_source_all_deterministic_atoms_compensator_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every countable deterministic fine-grid clock is null for both the
stopped literal original source occupation and its canonical intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ D : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] D →
        μ D = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) D) ∧
      (∀ (times : ℕ → ℝ≥0) (A : Set Ω),
        (∀ n : ℕ, MeasurableSet[𝓕.rightCont.predictable]
          ({times n} ×ˢ A)) →
        ∀ (B : Set ℝ), MeasurableSet B →
        MT (((Set.range times) ×ˢ A) ×ˢ B) =
          (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
           μ.prod (X.ν.restrict (Iio (0 : ℝ))))
            (((Set.range times) ×ˢ A) ×ˢ B) ∧
        MT (((Set.range times) ×ˢ A) ×ˢ B) = 0) := by
  obtain ⟨μ, hfin, hagree, hatom⟩ :=
    avram_wave5_01_actual_rightcont_stopped_source_all_deterministic_atoms_compensator_zero
      X K hK M hM S MT hMT T
  refine ⟨μ, hfin, hagree, ?_⟩
  intro times A hPred B hB
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let C : ℕ → Set ((ℝ≥0 × Ω) × ℝ) :=
    fun n => (({times n} ×ˢ A) ×ˢ B)
  have hUnion :
      (((Set.range times) ×ˢ A) ×ˢ B) = ⋃ n : ℕ, C n := by
    ext ⟨⟨t, ω⟩, z⟩
    simp only [C, Set.mem_prod, Set.mem_range, Set.mem_iUnion,
      Set.mem_singleton_iff]
    aesop
  have hMTatom (n : ℕ) : MT (C n) = 0 :=
    (hatom (times n) A (hPred n) B hB).2
  have hNatom (n : ℕ) :
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) (C n) = 0 := by
    have h := (hatom (times n) A (hPred n) B hB).1
    change MT (C n) =
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) (C n) at h
    rw [← h]
    exact hMTatom n
  have hMTzero :
      MT (((Set.range times) ×ˢ A) ×ˢ B) = 0 := by
    rw [hUnion]
    exact measure_iUnion_null hMTatom
  have hNzero :
      (μ.prod (X.ν.restrict (Iio (0 : ℝ))))
        (((Set.range times) ×ˢ A) ×ˢ B) = 0 := by
    rw [hUnion]
    exact measure_iUnion_null hNatom
  exact ⟨hMTzero.trans hNzero.symm, hMTzero⟩
