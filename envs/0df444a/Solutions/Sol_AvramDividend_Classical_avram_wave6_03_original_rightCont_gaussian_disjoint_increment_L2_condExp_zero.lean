-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_increment_L2_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:48:16.609093+00:00
-- url     : https://prove2.me/submissions/168c3a5f-ab14-403b-956a-a73d783f22a7

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
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    MemLp Y₁ 2 P ∧ MemLp Y₂ 2 P ∧
    Integrable (Y₁ * Y₂) P ∧
      (P[Y₁ * Y₂ | 𝓕.rightCont u] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y₁ : Ω → ℝ := fun ω =>
    X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  let Y₂ : Ω → ℝ := fun ω =>
    X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
  have hsevents : ∀ w : ℝ≥0,
      MeasurableSet[𝓕.rightCont w] {ω : Ω | (fun _ : Ω => s) ω ≤ w} := by
    intro w
    by_cases hsw : s ≤ w <;> simp [hsw]
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
  have huevents : ∀ w : ℝ≥0,
      MeasurableSet[𝓕.rightCont w] {ω : Ω | (fun _ : Ω => u) ω ≤ w} := by
    intro w
    by_cases huw : u ≤ w <;> simp [huw]
  have hustop : IsStoppingTime 𝓕.rightCont
      (fun ω => ((fun _ : Ω => u) ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events (fun _ : Ω => u) huevents
  have hubound : ∀ ω : Ω, (fun _ : Ω => u) ω ≤ u :=
    fun _ => le_rfl
  have hY₂Mem : MemLp Y₂ 2 P := by
    have hm :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν (fun _ : Ω => u) hustop u hubound (v - u)
    simpa only [Y₂, add_tsub_cancel_of_le huv, NNReal.coe_sub huv] using hm
  have hProdI : Integrable (Y₁ * Y₂) P :=
    hY₁Mem.integrable_mul hY₂Mem
  have hsMeas : Measurable[𝓕.rightCont u] (X.X s) :=
    (X.adapted s).mono
      ((𝓕.mono (hst.trans htu)).trans (𝓕.le_rightCont u)) le_rfl
  have htMeas : Measurable[𝓕.rightCont u] (X.X t) :=
    (X.adapted t).mono ((𝓕.mono htu).trans (𝓕.le_rightCont u)) le_rfl
  have hY₁Strong : StronglyMeasurable[𝓕.rightCont u] Y₁ :=
    ((htMeas.sub hsMeas).sub_const (((t - s) : ℝ) * X.c)).stronglyMeasurable
  have hY₂Pair :=
    avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
      X hν u v huv
  change Integrable Y₂ P ∧
    (P[Y₂ | 𝓕.rightCont u] =ᵐ[P] (fun _ => (0 : ℝ))) at hY₂Pair
  have hPull : P[Y₁ * Y₂ | 𝓕.rightCont u] =ᵐ[P]
      Y₁ * P[Y₂ | 𝓕.rightCont u] :=
    condExp_mul_of_stronglyMeasurable_left hY₁Strong hProdI hY₂Pair.1
  change MemLp Y₁ 2 P ∧ MemLp Y₂ 2 P ∧
    Integrable (Y₁ * Y₂) P ∧
      (P[Y₁ * Y₂ | 𝓕.rightCont u] =ᵐ[P] (fun _ => (0 : ℝ)))
  refine ⟨hY₁Mem, hY₂Mem, hProdI, ?_⟩
  filter_upwards [hPull, hY₂Pair.2] with ω hp hz
  calc
    (P[Y₁ * Y₂ | 𝓕.rightCont u]) ω =
        (Y₁ * P[Y₂ | 𝓕.rightCont u]) ω := hp
    _ = Y₁ ω * (P[Y₂ | 𝓕.rightCont u]) ω := rfl
    _ = 0 := by rw [hz]; ring
