-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:47:28.905409+00:00
-- url     : https://prove2.me/submissions/fa2571a7-6d8c-4f81-93a2-1f06854278f9



import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The finite genuine original source expected jump count on any interval is a finite mark measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (hFiniteMean :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤) :
    ∃ μ : Measure ℝ, μ Set.univ < ⊤ ∧
      ∀ B : Set ℝ, MeasurableSet B →
        μ B = (∫⁻ ω,
          ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) := by
  classical
  obtain ⟨M, hM⟩ :=
    AvramDividend.Classical.avram_wave6_01_original_event_weighted_marked_count_is_measure
      X Set.univ MeasurableSet.univ
  let A : Set (ℝ≥0 × ℝ) := Ioc s t ×ˢ Iic (-ε)
  let μ : Measure ℝ := (M.restrict A).map Prod.snd
  have hA : MeasurableSet A := measurableSet_Ioc.prod measurableSet_Iic
  have hμ_univ : μ Set.univ = M A := by
    change ((M.restrict A).map Prod.snd) Set.univ = M A
    calc
      ((M.restrict A).map Prod.snd) Set.univ =
          (M.restrict A) Set.univ := by
        rw [Measure.map_apply measurable_snd MeasurableSet.univ]
        rfl
      _ = M A := by simp
  refine ⟨μ, ?_, ?_⟩
  · rw [hμ_univ, hM A hA]
    simpa using hFiniteMean
  · intro B hB
    have hAB : MeasurableSet (Ioc s t ×ˢ (B ∩ Iic (-ε))) :=
      measurableSet_Ioc.prod (hB.inter measurableSet_Iic)
    have hInter :
        Prod.snd ⁻¹' B ∩ A =
          Ioc s t ×ˢ (B ∩ Iic (-ε)) := by
      ext p
      rcases p with ⟨u, y⟩
      simp only [A, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
        Prod.snd, and_assoc, and_left_comm, and_comm]
    have hPre : MeasurableSet (Prod.snd ⁻¹' B) :=
      hB.preimage (measurable_snd : Measurable (Prod.snd : ℝ≥0 × ℝ → ℝ))
    calc
      μ B = M (Prod.snd ⁻¹' B ∩ A) := by
        change ((M.restrict A).map Prod.snd) B = _
        rw [Measure.map_apply measurable_snd hB,
          Measure.restrict_apply hPre]
      _ = M (Ioc s t ×ˢ (B ∩ Iic (-ε))) := by exact congrArg (fun C : Set (ℝ≥0 × ℝ) => M C) hInter
      _ = (∫⁻ ω in Set.univ,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) :=
        hM _ hAB
      _ = _ := by simp