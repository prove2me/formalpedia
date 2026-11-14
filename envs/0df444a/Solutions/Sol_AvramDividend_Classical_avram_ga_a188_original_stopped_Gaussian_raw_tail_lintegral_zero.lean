-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a188_original_stopped_Gaussian_raw_tail_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:09:18.572754+00:00
-- url     : https://prove2.me/submissions/b72a3ded-64e8-4ec9-a897-ada8c9a80035

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a189_original_stopped_raw_large_tail_ennreal_finset_sum_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The already Proved original Gaussian source stopped-tail ENNReal limit
is exactly the ENNReal integral of the true real squared tail source sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (η : ℝ) (hη : 0 < η) :
    let Tail : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω then (if η ≤ |r| then r^2 else 0) else 0
    Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (Tail m ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  intro Tail
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω
  have hSource := avram_ga_a189_original_stopped_raw_large_tail_ennreal_finset_sum_tendsto
    X hν hσ n ρ hρstop η hη
  change Tendsto (fun m : ℕ => ∫⁻ ω, ∑ i ∈ Finset.range m,
    if s m i < ρ ω then
      ENNReal.ofReal (if η ≤ |R m i ω| then (R m i ω)^2 else 0)
    else 0 ∂P) atTop (𝓝 (0 : ℝ≥0∞)) at hSource
  have hEq (m : ℕ) (ω : Ω) :
      ENNReal.ofReal (Tail m ω) =
        ∑ i ∈ Finset.range m, if s m i < ρ ω then
          ENNReal.ofReal (if η ≤ |R m i ω| then (R m i ω)^2 else 0)
        else 0 := by
    change ENNReal.ofReal (∑ i ∈ Finset.range m,
      if s m i < ρ ω then (if η ≤ |R m i ω| then (R m i ω)^2 else 0)
      else 0) = _
    rw [ENNReal.ofReal_sum_of_nonneg (by
      intro i hi
      split_ifs <;> positivity)]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : s m i < ρ ω
    · simp only [if_pos ha]
    · simp only [if_neg ha, ENNReal.ofReal_zero]
  convert hSource using 1
  funext m
  exact lintegral_congr (fun ω => hEq m ω)
