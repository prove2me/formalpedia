-- Prove2me | solution 1 for ChenStein.Process.Ti_comp_Si
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:54:52.838155+00:00
-- url     : https://prove2.me/submissions/e2dc73fd-7894-4f70-a9ad-ae5d6f217c59

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting



namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

lemma Si_eq_zero {d : ℕ} (i : Fin d) (lj : ℝ≥0) (h : (Fin d → ℕ) → ℝ)
    (j : Fin d → ℕ) (hj : j i = 0) : Si i lj h j = 0 := by
  simp [Si, hj]

lemma Si_eq_succ {d : ℕ} (i : Fin d) (lj : ℝ≥0) (h : (Fin d → ℕ) → ℝ)
    (j : Fin d → ℕ) (n : ℕ) (hj : j i = n + 1) :
    Si i lj h j = -((lj : ℝ) * (poissonMeasure lj).real {n})⁻¹ *
      ∑ k ∈ Finset.range (n + 1), h (Function.update j i k) * (poissonMeasure lj).real {k} := by
  simp [Si, hj]

lemma add_e_apply {d : ℕ} (i : Fin d) (j : Fin d → ℕ) : (j + e i) i = j i + 1 := by
  simp [e]

lemma update_add_e {d : ℕ} (i : Fin d) (j : Fin d → ℕ) (k : ℕ) :
    Function.update (j + e i) i k = Function.update j i k := by
  ext m
  by_cases hm : m = i
  · subst hm; simp
  · simp [Function.update_of_ne hm, e, Pi.single_eq_of_ne hm]

lemma poisson_real_succ (lj : ℝ≥0) (n : ℕ) :
    (poissonMeasure lj).real {n + 1} = (lj : ℝ) * (poissonMeasure lj).real {n} / (n + 1) := by
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem Ti_comp_Si_core {d : ℕ} (i : Fin d) (lj : ℝ≥0) (hlj : 0 < lj)
    (h : (Fin d → ℕ) → ℝ) :
    ∀ j, Ti i lj (Si i lj h) j = h j := by
  intro j
  have hpos : ∀ n, 0 < (poissonMeasure lj).real {n} :=
    fun n => poissonMeasure_real_singleton_pos n hlj
  have hlj' : (0 : ℝ) < lj := hlj
  unfold Ti
  rcases hn : j i with _ | n
  · rw [Si_eq_zero i lj h j hn, Si_eq_succ i lj h (j + e i) 0 (by rw [add_e_apply, hn])]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, update_add_e]
    have h0 := hpos 0
    have hj0 : Function.update j i 0 = j := by
      rw [← hn]; exact Function.update_eq_self i j
    rw [hj0]
    field_simp
    ring
  · rw [Si_eq_succ i lj h j n hn, Si_eq_succ i lj h (j + e i) (n + 1) (by rw [add_e_apply, hn])]
    simp only [update_add_e]
    rw [Finset.sum_range_succ _ (n + 1), poisson_real_succ]
    have hjn : Function.update j i (n + 1) = j := by
      rw [← hn]; exact Function.update_eq_self i j
    rw [hjn]
    have h0 := hpos n
    field_simp
    push_cast
    ring

end ChenStein.Process

open ChenStein.Process
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {d : ℕ} (i : Fin d) (lj : ℝ≥0) (hlj : 0 < lj)
    (h : (Fin d → ℕ) → ℝ) :
    ∀ j, Ti i lj (Si i lj h) j = h j := by
  exact Ti_comp_Si_core i lj hlj h
