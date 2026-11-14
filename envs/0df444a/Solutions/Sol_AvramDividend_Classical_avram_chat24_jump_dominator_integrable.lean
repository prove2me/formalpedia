-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_jump_dominator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:14:56.243557+00:00
-- url     : https://prove2.me/submissions/10aff467-35de-40d0-8aa9-f49b6ff12042

import Mathlib
import Theorems.Thm_avram_chat24_right_path_measurable_core
import Theorems.Thm_avram_chat24_left_limit_measurable_core
import Theorems.Thm_avram_chat24_mapped_jump_cell_integral_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (f : ℝ≥0 → ℝ) (B : ℝ≥0) (L : ℝ≥0)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0)) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ f u - Function.leftLim f u ≠ 0}).map
        (fun u : ℝ≥0 => (u, f u - Function.leftLim f u)))
    let Jdom : ℝ≥0 × ℝ → ℝ := fun p =>
      if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then (L : ℝ) * (-p.2) else 0
    Integrable Jdom NX := by
  classical
  intro NX Jdom
  let Δ : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
  have hΔ : Measurable Δ :=
    (avram_chat24_right_path_measurable_core f hf_right).sub
      (avram_chat24_left_limit_measurable_core f hf_left)
  have hdown (t : ℝ≥0) (ht : 0 < t) : Δ t ≤ 0 :=
    sub_nonpos.mpr (hf_down t ht)
  have hsum' : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then -Δ t else 0) := by
    simpa only [Δ, neg_sub] using hsum
  let H : ℝ≥0 × ℝ → ℝ := fun p => if 0 < p.1 ∧ p.1 ≤ B then -p.2 else 0
  have hbase : Integrable H NX :=
    (avram_chat24_mapped_jump_cell_integral_core Δ hΔ hdown 0 B hsum').1
  have hneg : MeasurableSet {p : ℝ≥0 × ℝ | p.2 < 0} :=
    measurableSet_lt measurable_snd measurable_const
  have hprod := (hbase.indicator hneg).const_mul (L : ℝ)
  convert hprod using 1
  ext p
  by_cases hp0 : 0 < p.1 <;> by_cases hpB : p.1 ≤ B <;>
    by_cases hpn : p.2 < 0 <;> simp [Jdom, H, Set.indicator, hp0, hpB, hpn]
