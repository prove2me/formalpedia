-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_original_strict_intrinsic_marked_magnitude_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:02:30.915018+00:00
-- url     : https://prove2.me/submissions/36f70b4f-6e59-4149-a0c0-3e9bd08c53f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! The canonical strict marked integral equals its actual finite physical mark sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))}
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
        X ω T k).toFinset
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S, ENNReal.ofReal (-(X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  classical
  let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
      -(1 / ((k : ℝ) + 1))}
  have hFin : J.Finite :=
    AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
      X ω T k
  let S : Finset ℝ≥0 := hFin.toFinset
  let f : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
    then ENNReal.ofReal (-p.2) else 0
  have h₁ : MeasurableSet {p : ℝ≥0 × ℝ | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have h₂ : MeasurableSet {p : ℝ≥0 × ℝ | p.1 ≤ T} :=
    measurableSet_le measurable_fst measurable_const
  have h₃ : MeasurableSet {p : ℝ≥0 × ℝ |
      p.2 < -(1 / ((k : ℝ) + 1))} :=
    measurableSet_lt measurable_snd measurable_const
  have hset : MeasurableSet {p : ℝ≥0 × ℝ |
      0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))} :=
    h₁.inter (h₂.inter h₃)
  have hf : Measurable f := by
    change Measurable (fun p : ℝ≥0 × ℝ =>
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0)
    exact Measurable.ite hset
      (ENNReal.measurable_ofReal.comp (measurable_neg.comp measurable_snd))
      measurable_const
  have h := AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
    X ω f hf
  change (∫⁻ p : ℝ≥0 × ℝ, f p ∂
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S, ENNReal.ofReal (-(X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  rw [h]
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro u hu
    have hJ : u ∈ J := (hFin.mem_toFinset).mp hu
    change 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1)) at hJ
    have hcut : -(1 / ((k : ℝ) + 1)) ≤ 0 :=
      neg_nonpos.mpr (by positivity)
    have hNZ : X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 :=
      ne_of_lt (lt_of_lt_of_le hJ.2.2 hcut)
    change (if 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
      then f (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      else 0) =
        ENNReal.ofReal (-(X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    rw [if_pos ⟨hJ.1, hNZ⟩]
    change (if 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-(X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0) =
      ENNReal.ofReal (-(X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    rw [if_pos hJ]
  · intro u hu
    have hNot : u ∉ J := by
      intro hJ
      exact hu ((hFin.mem_toFinset).mpr hJ)
    change ¬(0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))) at hNot
    change (if 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
      then f (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      else 0) = 0
    by_cases hNZ : 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
    · rw [if_pos hNZ]
      change (if 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
          -(1 / ((k : ℝ) + 1))
        then ENNReal.ofReal (-(X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0) = 0
      rw [if_neg hNot]
    · rw [if_neg hNZ]
