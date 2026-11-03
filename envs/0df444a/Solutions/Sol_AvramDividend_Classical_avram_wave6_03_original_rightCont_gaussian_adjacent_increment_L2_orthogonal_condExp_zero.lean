-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_adjacent_increment_L2_orthogonal_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:43:31.527968+00:00
-- url     : https://prove2.me/submissions/293d3baf-6aa3-420f-9fb5-32eb250402f8

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X u ω - X.X t ω - ((u - t) : ℝ) * X.c
    MemLp Y₁ 2 P ∧ MemLp Y₂ 2 P ∧
    Integrable (Y₁ * Y₂) P ∧
      (P[Y₁ * Y₂ | 𝓕.rightCont t] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y₁ : Ω → ℝ := fun ω =>
    X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  let Y₂ : Ω → ℝ := fun ω =>
    X.X u ω - X.X t ω - ((u - t) : ℝ) * X.c
  have hsevents : ∀ v : ℝ≥0,
      MeasurableSet[𝓕.rightCont v] {ω : Ω | (fun _ : Ω => s) ω ≤ v} := by
    intro v
    by_cases hsv : s ≤ v <;> simp [hsv]
  have hsstop : IsStoppingTime 𝓕.rightCont
      (fun ω => ((fun _ : Ω => s) ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events (fun _ : Ω => s) hsevents
  have hsbound : ∀ ω : Ω, (fun _ : Ω => s) ω ≤ s :=
    fun _ => le_rfl
  have hY₁Mem : MemLp Y₁ 2 P := by
    have hm :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν (fun _ : Ω => s) hsstop s hsbound (t - s)
    simpa only [Y₁, add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using hm
  have htevents : ∀ v : ℝ≥0,
      MeasurableSet[𝓕.rightCont v] {ω : Ω | (fun _ : Ω => t) ω ≤ v} := by
    intro v
    by_cases htv : t ≤ v <;> simp [htv]
  have htstop : IsStoppingTime 𝓕.rightCont
      (fun ω => ((fun _ : Ω => t) ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events (fun _ : Ω => t) htevents
  have htbound : ∀ ω : Ω, (fun _ : Ω => t) ω ≤ t :=
    fun _ => le_rfl
  have hY₂Mem : MemLp Y₂ 2 P := by
    have hm :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν (fun _ : Ω => t) htstop t htbound (u - t)
    simpa only [Y₂, add_tsub_cancel_of_le htu, NNReal.coe_sub htu] using hm
  have hProdI : Integrable (Y₁ * Y₂) P :=
    hY₁Mem.integrable_mul hY₂Mem
  have hsMeas : Measurable[𝓕.rightCont t] (X.X s) :=
    (X.adapted s).mono ((𝓕.mono hst).trans (𝓕.le_rightCont t)) le_rfl
  have htMeas : Measurable[𝓕.rightCont t] (X.X t) :=
    (X.adapted t).mono (𝓕.le_rightCont t) le_rfl
  have hY₁Strong : StronglyMeasurable[𝓕.rightCont t] Y₁ :=
    ((htMeas.sub hsMeas).sub_const (((t - s) : ℝ) * X.c)).stronglyMeasurable
  have hY₂Pair :=
    avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
      X hν t u htu
  change Integrable Y₂ P ∧
    (P[Y₂ | 𝓕.rightCont t] =ᵐ[P] (fun _ => (0 : ℝ))) at hY₂Pair
  have hPull : P[Y₁ * Y₂ | 𝓕.rightCont t] =ᵐ[P]
      Y₁ * P[Y₂ | 𝓕.rightCont t] :=
    condExp_mul_of_stronglyMeasurable_left hY₁Strong hProdI hY₂Pair.1
  change MemLp Y₁ 2 P ∧ MemLp Y₂ 2 P ∧
    Integrable (Y₁ * Y₂) P ∧
      (P[Y₁ * Y₂ | 𝓕.rightCont t] =ᵐ[P] (fun _ => (0 : ℝ)))
  refine ⟨hY₁Mem, hY₂Mem, hProdI, ?_⟩
  filter_upwards [hPull, hY₂Pair.2] with ω hp hz
  calc
    (P[Y₁ * Y₂ | 𝓕.rightCont t]) ω =
        (Y₁ * P[Y₂ | 𝓕.rightCont t]) ω := hp
    _ = Y₁ ω * (P[Y₂ | 𝓕.rightCont t]) ω := rfl
    _ = 0 := by rw [hz]; ring
