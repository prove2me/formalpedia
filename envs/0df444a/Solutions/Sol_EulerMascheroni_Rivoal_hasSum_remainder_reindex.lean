-- Prove2me | solution 1 for EulerMascheroni.Rivoal.hasSum_remainder_reindex
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:21:40.809019+00:00
-- url     : https://prove2.me/submissions/d14709f2-c69d-4eb3-91c0-2b4fffbe8f47

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_eulerMascheroni_rivoalForms

open Finset

lemma RivoalSeriesAux.prod_sub_mul_factorial (x : ℕ) : ∀ k, k ≤ x →
    (∏ t ∈ range k, ((x : ℝ) - t)) * ((x - k).factorial : ℝ) = x.factorial := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [prod_range_succ, ← ih (by omega)]
    have : x - k = (x - (k + 1)) + 1 := by omega
    rw [this, Nat.factorial_succ]
    push_cast
    rw [show ((x - (k + 1) : ℕ) : ℝ) = (x : ℝ) - k - 1 by
      rw [Nat.cast_sub hk]; push_cast; ring]
    ring

theorem solution (n : ℕ) :
    HasSum (fun M : ℕ => if n + 1 ≤ M then
        (-1 : ℝ) ^ M * ((∏ i ∈ Ico (n + 1) (3 * n + 1), ((M : ℝ) - i)) /
          (∏ i ∈ range (n + 1), ((M : ℝ) - i))) / (M.factorial : ℝ) else 0)
      ((-1) ^ (n + 1) * EulerMascheroni.Rivoal.remainder n) := by
  set g : ℕ → ℝ := fun M => if n + 1 ≤ M then
        (-1 : ℝ) ^ M * ((∏ i ∈ Ico (n + 1) (3 * n + 1), ((M : ℝ) - i)) /
          (∏ i ∈ range (n + 1), ((M : ℝ) - i))) / (M.factorial : ℝ) else 0 with hg
  set f : ℕ → ℝ := fun m => (-1 : ℝ) ^ m / (m.factorial : ℝ) *
    (((m + 2 * n).factorial : ℝ) / ((m + 3 * n + 1).factorial : ℝ)) ^ 2 with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial 1) (fun m => ?_)
    have ha0 : (0 : ℝ) ≤ ((m + 2 * n).factorial : ℝ) / ((m + 3 * n + 1).factorial : ℝ) := by
      positivity
    have ha1 : ((m + 2 * n).factorial : ℝ) / ((m + 3 * n + 1).factorial : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast Nat.factorial_le (by omega)
    rw [hf]; dsimp only
    simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast,
      Real.norm_of_nonneg ha0]
    have h2 : (((m + 2 * n).factorial : ℝ) / ((m + 3 * n + 1).factorial : ℝ)) ^ 2 ≤ 1 := by
      nlinarith
    have : (0:ℝ) ≤ 1 / (m.factorial : ℝ) := by positivity
    nlinarith
  have hrem : HasSum f (EulerMascheroni.Rivoal.remainder n) := hfs.hasSum
  rw [← hasSum_nat_add_iff' (3 * n + 1)]
  have hz : ∑ i ∈ range (3 * n + 1), g i = 0 := by
    refine sum_eq_zero (fun i hi => ?_)
    have hi' := mem_range.mp hi
    rw [hg]; dsimp only
    split_ifs with h
    · rw [prod_eq_zero (i := i) (mem_Ico.mpr ⟨h, hi'⟩) (sub_self _)]; simp
    · rfl
  rw [hz, sub_zero]
  refine (hrem.mul_left ((-1 : ℝ) ^ (n + 1))).congr_fun ?_
  intro m
  rw [hg, hf]; dsimp only
  rw [if_pos (by omega)]
  -- numerator
  have hN : (∏ i ∈ Ico (n + 1) (3 * n + 1), (((m + (3 * n + 1) : ℕ) : ℝ) - i)) *
      (m.factorial : ℝ) = ((m + 2 * n).factorial : ℝ) := by
    rw [prod_Ico_eq_prod_range, show 3 * n + 1 - (n + 1) = 2 * n by omega]
    have := RivoalSeriesAux.prod_sub_mul_factorial (m + 2 * n) (2 * n) (by omega)
    rw [show m + 2 * n - 2 * n = m by omega] at this
    rw [← this]
    congr 1
    refine prod_congr rfl (fun t _ => ?_)
    push_cast; ring
  have hD : (∏ i ∈ range (n + 1), (((m + (3 * n + 1) : ℕ) : ℝ) - i)) *
      ((m + 2 * n).factorial : ℝ) = ((m + 3 * n + 1).factorial : ℝ) := by
    have := RivoalSeriesAux.prod_sub_mul_factorial (m + (3 * n + 1)) (n + 1) (by omega)
    rw [show m + (3 * n + 1) - (n + 1) = m + 2 * n by omega,
      show m + (3 * n + 1) = m + 3 * n + 1 by omega] at this
    rw [show m + (3 * n + 1) = m + 3 * n + 1 by omega]
    exact this
  have e1 : (∏ i ∈ Ico (n + 1) (3 * n + 1), (((m + (3 * n + 1) : ℕ) : ℝ) - i)) =
      ((m + 2 * n).factorial : ℝ) / (m.factorial : ℝ) := by
    rw [← hN]; field_simp
  have e2 : (∏ i ∈ range (n + 1), (((m + (3 * n + 1) : ℕ) : ℝ) - i)) =
      ((m + 3 * n + 1).factorial : ℝ) / ((m + 2 * n).factorial : ℝ) := by
    rw [← hD]; field_simp
  rw [e1, e2, show m + (3 * n + 1) = m + 3 * n + 1 by omega]
  have hMf : ((m + 3 * n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hmf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hkf : ((m + 2 * n).factorial : ℝ) ≠ 0 := by positivity
  rw [show m + 3 * n + 1 = m + (3 * n + 1) by omega, pow_add,
    show 3 * n + 1 = 2 * n + (n + 1) by omega, pow_add,
    show (2 * n) = n * 2 by ring, pow_mul]
  field_simp
  rw [← pow_mul, mul_comm, pow_mul]; norm_num
