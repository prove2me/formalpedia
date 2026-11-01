-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_first_record_clock_joint_height_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:42:10.613744+00:00
-- url     : https://prove2.me/submissions/65ffc2c1-bb4a-4f7c-ad7d-082775fe91ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Joint Borel measurability of the genuine strict-record height clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun p : ℝ × Ω => twoSidedExitUpTime X p.1 p.2) := by
  classical
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hSample (j : ℕ) :
      Measurable (fun p : ℝ × Ω => X.X (samples j) p.2) := by
    exact (chat04_levy_joint_time_state_measurable X).comp
      (measurable_const.prodMk measurable_snd)
  have hEach (j : ℕ) : Measurable (fun p : ℝ × Ω =>
      if p.1 < X.X (samples j) p.2 then (samples j : ℝ≥0∞)
      else ⊤) := by
    exact Measurable.ite (measurableSet_lt measurable_fst (hSample j))
      measurable_const measurable_const
  have hCount : Measurable (fun p : ℝ × Ω =>
      ⨅ j : ℕ, if p.1 < X.X (samples j) p.2 then
          (samples j : ℝ≥0∞) else ⊤) :=
    Measurable.iInf hEach
  have hClock (p : ℝ × Ω) :
      twoSidedExitUpTime X p.1 p.2 =
      (⨅ j : ℕ, if p.1 < X.X (samples j) p.2 then
          (samples j : ℝ≥0∞) else ⊤) := by
    have hzero : X.X 0 p.2 = 0 := X.X_zero p.2
    have hp := avram_wave3_01_true_shifted_record_ruin_clock_pair
      X p.2 0 1 p.1
    dsimp at hp
    simp only [zero_add, hzero, sub_zero] at hp
    let f : ℝ≥0 → ℝ := fun t => X.X t p.2
    let ρ : ℝ≥0∞ := ⨅ i : ℕ,
      if p.1 < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
    have hρ : ρ = twoSidedExitUpTime X p.1 p.2 := by
      simpa [ρ, f, samples, twoSidedExitUpTime, zero_add, hzero,
        iInf_subtype] using (congrArg Prod.fst hp).symm
    simpa [ρ, f, hzero] using hρ.symm
  have heq :
      (fun p : ℝ × Ω =>
        ⨅ j : ℕ, if p.1 < X.X (samples j) p.2 then
          (samples j : ℝ≥0∞) else ⊤) =
      (fun p : ℝ × Ω => twoSidedExitUpTime X p.1 p.2) := by
    funext p
    exact (hClock p).symm
  rw [← heq]
  exact hCount
