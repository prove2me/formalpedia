-- Prove2me | solution 1 for EulerMascheroni.Rivoal.remainder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:16:31.54397+00:00
-- url     : https://prove2.me/submissions/fe62d268-ac26-4aa9-adb5-14e95320d137

import Definitions.Def_eulerMascheroni_rivoalForms
import Mathlib.Analysis.SpecificLimits.Normed

open Finset Filter Topology

namespace RivoalRemainderAux

/-- `a_m = (m+2n)!/(m+3n+1)!`. -/
noncomputable def a (n m : ℕ) : ℝ := ((m + 2 * n).factorial : ℝ) / ((m + 3 * n + 1).factorial : ℝ)

/-- `t_m = a_m^2 / m!`. -/
noncomputable def t (n m : ℕ) : ℝ := a n m ^ 2 / (m.factorial : ℝ)

lemma a_pos (n m : ℕ) : 0 < a n m := by unfold a; positivity

lemma a_succ (n m : ℕ) :
    a n (m + 1) = a n m * (((m + 2 * n + 1 : ℕ) : ℝ) / ((m + 3 * n + 2 : ℕ) : ℝ)) := by
  unfold a
  rw [show m + 1 + 2 * n = (m + 2 * n) + 1 by ring, show m + 1 + 3 * n + 1 = (m + 3 * n + 1) + 1 by ring,
    Nat.factorial_succ, Nat.factorial_succ (m + 3 * n + 1)]
  have h1 : ((m + 3 * n + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((m + 3 * n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at *
  field_simp
  ring

lemma a_le_one (n m : ℕ) : a n m ≤ 1 := by
  unfold a
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.factorial_le (by omega)

lemma a_succ_le (n m : ℕ) : a n (m + 1) ≤ a n m := by
  rw [a_succ]
  have := a_pos n m
  have hq : (((m + 2 * n + 1 : ℕ) : ℝ) / ((m + 3 * n + 2 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast (by omega)
  nlinarith

lemma t_nonneg (n m : ℕ) : 0 ≤ t n m := by unfold t; have := a_pos n m; positivity

lemma t_antitone (n : ℕ) : Antitone (t n) := by
  refine antitone_nat_of_succ_le (fun m => ?_)
  unfold t
  have h0 := a_pos n (m + 1)
  have h1 := a_succ_le n m
  have hf : (m.factorial : ℝ) ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
  have hsq : a n (m + 1) ^ 2 ≤ a n m ^ 2 := by gcongr
  calc a n (m + 1) ^ 2 / ((m + 1).factorial : ℝ) ≤ a n m ^ 2 / ((m + 1).factorial : ℝ) := by gcongr
    _ ≤ a n m ^ 2 / (m.factorial : ℝ) := by gcongr

lemma t_summable (n : ℕ) : Summable (t n) := by
  have hs := Real.summable_pow_div_factorial 1
  refine Summable.of_nonneg_of_le (t_nonneg n) (fun m => ?_) hs
  unfold t
  simp only [one_pow]
  have := a_pos n m
  have h1 := a_le_one n m
  have : a n m ^ 2 ≤ 1 := by nlinarith
  gcongr

lemma t_one_lt (n : ℕ) : t n 1 < t n 0 := by
  unfold t
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
  have e := a_succ n 0
  simp only [zero_add] at e
  rw [e]
  have h0 := a_pos n 0
  have hq0 : 0 < (((2 * n + 1 : ℕ) : ℝ) / ((3 * n + 2 : ℕ) : ℝ)) := by positivity
  have hq : (((2 * n + 1 : ℕ) : ℝ) / ((3 * n + 2 : ℕ) : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]; exact_mod_cast (by omega)
  have : a n 0 * (((2 * n + 1 : ℕ) : ℝ) / ((3 * n + 2 : ℕ) : ℝ)) < a n 0 := by nlinarith
  have hp : 0 < a n 0 * (((2 * n + 1 : ℕ) : ℝ) / ((3 * n + 2 : ℕ) : ℝ)) := by positivity
  nlinarith

lemma t_zero_le (n : ℕ) : t n 0 ≤ 1 / ((n + 1).factorial : ℝ) ^ 2 := by
  unfold t a
  simp only [zero_add, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [div_pow, one_div]
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  have hd : (2 * n).factorial * (n + 1).factorial ≤ (3 * n + 1).factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add (2 * n) (n + 1)
    rw [show 2 * n + (n + 1) = 3 * n + 1 by ring] at this
    exact Nat.le_of_dvd (Nat.factorial_pos _) this
  have hd' : ((2 * n).factorial : ℝ) * ((n + 1).factorial : ℝ) ≤ ((3 * n + 1).factorial : ℝ) := by
    exact_mod_cast hd
  have : (((2 * n).factorial : ℝ) * ((n + 1).factorial : ℝ)) ^ 2 ≤ ((3 * n + 1).factorial : ℝ) ^ 2 := by
    gcongr
  nlinarith [this]

lemma remainder_eq (n : ℕ) :
    EulerMascheroni.Rivoal.remainder n = ∑' m : ℕ, (-1 : ℝ) ^ m * t n m := by
  unfold EulerMascheroni.Rivoal.remainder t a
  congr 1; funext m; ring

end RivoalRemainderAux

open RivoalRemainderAux in
theorem solution (n : ℕ) :
    0 < EulerMascheroni.Rivoal.remainder n ∧
      EulerMascheroni.Rivoal.remainder n ≤ 1 / ((n + 1).factorial : ℝ) ^ 2 := by
  rw [remainder_eq]
  have hl := (t_summable n).tendsto_alternating_series_tsum
  have hlow := (t_antitone n).alternating_series_le_tendsto hl 1
  have hup := (t_antitone n).tendsto_le_alternating_series hl 0
  simp [Finset.sum_range_succ] at hlow hup
  refine ⟨?_, ?_⟩
  · have := t_one_lt n
    linarith
  · exact hup.trans (t_zero_le n)
