-- Prove2me | solution 1 for AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:47:57.581672+00:00
-- url     : https://prove2.me/submissions/b6601027-288f-410c-bae2-a759f4ae4b60

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t : ℝ≥0, Measurable (F t))
    (hRight : ∀ ω t, ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Ici t) t) :
    Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) := by
  let c : ℕ → ℝ≥0 → ℝ≥0 := fun n t => (⌈t * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n
  have hc_ge : ∀ n t, t ≤ c n t := by
    intro n t
    simp only [c]
    rw [le_div_iff₀ (by positivity)]
    exact Nat.le_ceil _
  have hc_le : ∀ n t, c n t ≤ t + 1 / 2 ^ n := by
    intro n t
    simp only [c]
    rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hmeas : ∀ n, Measurable (fun z : ℝ≥0 × Ω => F (c n z.1) z.2) := by
    intro n
    have h1 : Measurable (fun p : ℕ × Ω => F ((p.1 : ℝ≥0) / 2 ^ n) p.2) :=
      measurable_from_prod_countable_right (fun k => by simpa using hF ((k : ℝ≥0) / 2 ^ n))
    have h2 : Measurable (fun z : ℝ≥0 × Ω => (⌈z.1 * 2 ^ n⌉₊, z.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      exact Nat.measurable_ceil.comp (measurable_fst.mul_const _)
    exact h1.comp h2
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  rintro ⟨t, ω⟩
  have ht : Tendsto (fun n => c n t) atTop (𝓝[Ici t] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun n => hc_ge n t)⟩
    have hlim : Tendsto (fun n : ℕ => t + 1 / (2:ℝ≥0) ^ n) atTop (𝓝 t) := by
      have : Tendsto (fun n : ℕ => (1:ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
        simp only [one_div, ← inv_pow]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using tendsto_const_nhds.add this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (hc_ge · t) (hc_le · t)
  exact (hRight ω t).tendsto.comp ht
