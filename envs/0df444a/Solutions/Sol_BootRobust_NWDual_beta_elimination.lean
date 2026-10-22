-- Prove2me | solution 1 for BootRobust.NWDual.beta_elimination
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:07:00.963442+00:00
-- url     : https://prove2.me/submissions/3fc39c7a-9e95-4a94-aaf5-ad288f568d0a

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

set_option autoImplicit false

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (a : ι → ℝ) (ν : ℝ) (hν : 0 < ν) (r : ℝ) :
    (∀ β : ℝ,
      r * ν + ν * ∑ i, D i * Real.exp
          ((a i + (ν - ν * Real.log (∑ j, Real.exp (a j / ν) * D j))) / ν - 1) -
        (ν - ν * Real.log (∑ j, Real.exp (a j / ν) * D j)) ≤
      r * ν + ν * ∑ i, D i * Real.exp ((a i + β) / ν - 1) - β) ∧
    ((∃ β : ℝ, r * ν + ν * ∑ i, D i * Real.exp ((a i + β) / ν - 1) ≤ β) ↔
      ν * Real.log (∑ i, Real.exp (a i / ν) * D i) + r * ν ≤ 0) := by
  set S := ∑ j, Real.exp (a j / ν) * D j with hS
  have hSpos : 0 < S := by
    apply Finset.sum_pos'
    · intro i _; exact mul_nonneg (Real.exp_pos _).le (hD.1 i)
    · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := D)
        (by rw [hD.2]; exact one_ne_zero)
      exact ⟨i, Finset.mem_univ _, mul_pos (Real.exp_pos _) (lt_of_le_of_ne (hD.1 i) (Ne.symm hi))⟩
  have hsum : ∀ β : ℝ, ∑ i, D i * Real.exp ((a i + β) / ν - 1) = S * Real.exp (β / ν - 1) := by
    intro β
    rw [hS, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Real.exp ((a i + β) / ν - 1) = Real.exp (a i / ν) * Real.exp (β / ν - 1) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have hstar : ∑ i, D i * Real.exp ((a i + (ν - ν * Real.log S)) / ν - 1) = 1 := by
    rw [hsum]
    have : (ν - ν * Real.log S) / ν - 1 = -Real.log S := by field_simp; ring
    rw [this, Real.exp_neg, Real.exp_log hSpos]
    field_simp
  have hkey : ∀ β : ℝ, r * ν + ν * Real.log S ≤ r * ν + ν * (S * Real.exp (β / ν - 1)) - β := by
    intro β
    set t := β / ν - 1 + Real.log S with ht
    have h1 : S * Real.exp (β / ν - 1) = Real.exp t := by
      rw [ht, Real.exp_add, Real.exp_log hSpos]; ring
    have h2 := Real.add_one_le_exp t
    have h3 : β = ν * (t + 1 - Real.log S) := by rw [ht]; field_simp; ring
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left h2 hν.le]
  have hval : r * ν + ν * ∑ i, D i * Real.exp ((a i + (ν - ν * Real.log S)) / ν - 1) -
      (ν - ν * Real.log S) = r * ν + ν * Real.log S := by
    rw [hstar]; ring
  refine ⟨?_, ?_⟩
  · intro β
    rw [hval, hsum]
    exact hkey β
  · constructor
    · rintro ⟨β, hβ⟩
      rw [hsum] at hβ
      have := hkey β
      linarith
    · intro h
      refine ⟨ν - ν * Real.log S, ?_⟩
      have := hval
      linarith
