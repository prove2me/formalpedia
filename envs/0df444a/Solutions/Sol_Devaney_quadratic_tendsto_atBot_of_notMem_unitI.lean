-- Prove2me | solution 1 for Devaney.quadratic_tendsto_atBot_of_notMem_unitI
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T21:11:52.913247+00:00
-- url     : https://prove2.me/submissions/cf9154cc-37bb-499b-99e8-4d53929172bd

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DevFix

open Devaney Filter

/-- Below `0` the quadratic map overshoots the linear map `x ↦ μ x`. -/
theorem quadratic_lt_of_neg {μ x : ℝ} (hμ : 1 < μ) (hx : x < 0) :
    quadratic μ x ≤ μ * x ∧ quadratic μ x < 0 := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  have h1 : x * (1 - x) ≤ x := by nlinarith
  have h2 : quadratic μ x ≤ μ * x := by
    have : μ * (x * (1 - x)) ≤ μ * x := by nlinarith
    simpa [quadratic, mul_assoc] using this
  exact ⟨h2, by nlinarith⟩

/-- Iterating from a negative point, the orbit is dominated by the geometric sequence
`μⁿ x`. -/
theorem iterate_le_pow {μ x : ℝ} (hμ : 1 < μ) (hx : x < 0) :
    ∀ n : ℕ, (quadratic μ)^[n] x ≤ μ ^ n * x ∧ (quadratic μ)^[n] x < 0 := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  intro n
  induction n with
  | zero => exact ⟨by simp, by simpa using hx⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := quadratic_lt_of_neg hμ ih2
    rw [Function.iterate_succ_apply']
    refine ⟨?_, h2⟩
    calc quadratic μ ((quadratic μ)^[n] x) ≤ μ * (quadratic μ)^[n] x := h1
      _ ≤ μ * (μ ^ n * x) := by nlinarith
      _ = μ ^ (n + 1) * x := by ring

end DevFix

namespace Esc

open Devaney Filter DevFix

theorem escape_of_neg {μ x : ℝ} (hμ : 1 < μ) (hx : x < 0) :
    Tendsto (fun n : ℕ => (quadratic μ)^[n] x) atTop atBot := by
  have hpow : Tendsto (fun n : ℕ => μ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hμ
  have hmul : Tendsto (fun n : ℕ => μ ^ n * x) atTop atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg hx hpow
  exact tendsto_atBot_mono (fun n => (iterate_le_pow hμ hx n).1) hmul

/-- Proposition 5.2: an orbit starting outside `[0,1]` escapes to `-∞`. -/
theorem quadratic_tendsto_atBot_of_notMem_unitI (μ x : ℝ) (hμ : 1 < μ)
    (hx : x < 0 ∨ 1 < x) :
    Tendsto (fun n : ℕ => (quadratic μ)^[n] x) atTop atBot := by
  rcases hx with hx | hx
  · exact escape_of_neg hμ hx
  · have hneg : quadratic μ x < 0 := by
      have hμ0 : (0 : ℝ) < μ := by linarith
      have hq : quadratic μ x = μ * x * (1 - x) := rfl
      rw [hq]
      have h1 : (0:ℝ) < μ * x := by nlinarith
      have h2 : (1 : ℝ) - x < 0 := by linarith
      exact mul_neg_of_pos_of_neg h1 h2
    have h := escape_of_neg hμ hneg
    have hcongr : (fun n : ℕ => (quadratic μ)^[n] (quadratic μ x))
        = fun n : ℕ => (quadratic μ)^[n + 1] x := by
      funext n; rw [Function.iterate_succ_apply]
    rw [hcongr] at h
    exact (tendsto_add_atTop_iff_nat 1).mp h

end Esc

open Devaney Filter in
theorem solution (μ x : ℝ) (hμ : 1 < μ) (hx : x < 0 ∨ 1 < x) :
    Filter.Tendsto (fun n : ℕ => (quadratic μ)^[n] x) Filter.atTop Filter.atBot :=
  Esc.quadratic_tendsto_atBot_of_notMem_unitI μ x hμ hx
