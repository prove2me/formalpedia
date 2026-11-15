-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_finite_compensated_actual_marked_step_terminal_jump_right_left_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:14:47.293675+00:00
-- url     : https://prove2.me/submissions/24dcba53-d722-4204-b557-cd3c9b36ed66

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a30_single_mark_causal_step_left_limit_20261114
import Theorems.Thm_AvramDividend_Classical_avram_b24_actual_finite_mark_step_source_terminal_jump_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (d : ℝ)
    (Jsmall : ℝ≥0 → ℝ) (T t : ℝ≥0)
    (ht0 : 0 < t) (htT : t ≤ T)
    (hPath : ∀ v : ℝ≥0, v ≤ T →
      Jsmall v =
        (∑ u ∈ S,
          if u ≤ v then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (v : ℝ) * d) :
    Tendsto Jsmall (𝓝[<] t)
      (𝓝 ((∑ u ∈ S,
          if u < t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (t : ℝ) * d)) ∧
    Jsmall t -
      ((∑ u ∈ S,
          if u < t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (t : ℝ) * d) =
      if t ∈ S then (if -1 < z t ∧ z t < 0 then z t else 0) else 0  := by
  let a : ℝ≥0 → ℝ := fun u => if -1 < z u ∧ z u < 0 then z u else 0
  have hsum : Tendsto
      (fun v : ℝ≥0 => ∑ u ∈ S, if u ≤ v then a u else 0)
      (𝓝[<] t) (𝓝 (∑ u ∈ S, if u < t then a u else 0)) := by
    apply tendsto_finset_sum S
    intro u hu
    exact avram_a30_single_mark_causal_step_left_limit_20261114 u (a u) t ht0
  have hreal : Tendsto (fun v : ℝ≥0 => (v : ℝ))
      (𝓝[<] t) (𝓝 (t : ℝ)) :=
    (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto
      (fun v : ℝ≥0 => (∑ u ∈ S, if u ≤ v then a u else 0) -
        (v : ℝ) * d) (𝓝[<] t)
      (𝓝 ((∑ u ∈ S, if u < t then a u else 0) - (t : ℝ) * d)) :=
    hsum.sub (hreal.mul tendsto_const_nhds)
  have hevent : Jsmall =ᶠ[𝓝[<] t]
      (fun v : ℝ≥0 => (∑ u ∈ S, if u ≤ v then a u else 0) -
        (v : ℝ) * d) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    simpa only [a] using hPath v ((le_of_lt hv).trans htT)
  constructor
  · exact (Filter.tendsto_congr' hevent).2 hdiff
  · rw [hPath t htT]
    have hAtom := avram_b24_actual_finite_mark_step_source_terminal_jump_exact
      S (fun u => if -1 < z u ∧ z u < 0 then z u else 0) t
    linarith
