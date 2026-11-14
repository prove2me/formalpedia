-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a189_original_stopped_raw_large_tail_ennreal_finset_sum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:04:06.638195+00:00
-- url     : https://prove2.me/submissions/62921e68-d0ee-4360-87cd-754234c02469

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a56_original_stopped_raw_large_tail_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped raw tail extended finite sum is the Proved Gaussian
source ga56 tail, with exact raw and drift-centred increments identified. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (η : ℝ) (hη : 0 < η) :
    let Tail : ℕ → Ω → ℝ≥0∞ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω then ENNReal.ofReal
          (if η ≤ |r| then r^2 else 0) else 0
    Tendsto (fun m => ∫⁻ ω, Tail m ω ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  intro Tail
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    R m i ω - (Δ m : ℝ) * X.c
  have hw (m : ℕ) : (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1) := by
    simp only [Δ,NNReal.coe_div,NNReal.coe_add,
      NNReal.coe_natCast,NNReal.coe_one]
  have hm (m i : ℕ) (hi : i ∈ Finset.range m) :
      Measurable (fun ω => Z m i ω / X.σ) := by
    have h1 : Measurable (X.X (s m i + Δ m)) :=
      (X.adapted (s m i + Δ m)).mono (𝓕.le _) le_rfl
    have h0 : Measurable (X.X (s m i)) :=
      (X.adapted (s m i)).mono (𝓕.le _) le_rfl
    exact ((h1.sub h0).sub measurable_const).div_const _
  have hρ : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hSource := avram_ga_a56_original_stopped_raw_large_tail_tendsto
    X hν hσ n Δ hw hm ρ hρ η hη
  change Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
    if s m i < ρ ω then
      ENNReal.ofReal (if η ≤ |Z m i ω + (Δ m : ℝ) * X.c|
        then (Z m i ω + (Δ m : ℝ) * X.c)^2 else 0)
    else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) at hSource
  have hEq (m : ℕ) (ω : Ω) :
      Tail m ω =
        ∑ i ∈ Finset.range m,
          if s m i < ρ ω then
            ENNReal.ofReal (if η ≤ |Z m i ω + (Δ m : ℝ) * X.c|
              then (Z m i ω + (Δ m : ℝ) * X.c)^2 else 0)
          else 0 := by
    dsimp [Tail, Z, R, s, Δ]
    simp only [sub_add_cancel]
  convert hSource using 1
  funext m
  exact lintegral_congr (fun ω => hEq m ω)
