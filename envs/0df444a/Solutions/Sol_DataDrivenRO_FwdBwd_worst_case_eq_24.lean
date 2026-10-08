-- Prove2me | solution 1 for DataDrivenRO.FwdBwd.worst_case_eq_24
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:25:20.738602+00:00
-- url     : https://prove2.me/submissions/5d59d7ff-b6af-4168-b7e9-1fadbf1b8793

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

open DataDrivenRO.FwdBwd in
theorem solution {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    IsGreatest
      ((fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) => cssBound p.1 p.2.1 p.2.2 ε v) ''
        {p | ∀ i, (mb i ≤ p.1 i ∧ p.1 i ≤ mf i) ∧ (0 ≤ p.2.1 i ∧ p.2.1 i ≤ sf i) ∧
          (0 ≤ p.2.2 i ∧ p.2.2 i ≤ sb i)})
      (fbValue mb mf sf sb ε v) := by
  have hL : 0 ≤ 2 * Real.log (1 / ε) := by
    have : 1 < 1 / ε := by rw [lt_div_iff₀ hε0]; linarith
    have := Real.log_pos this
    linarith
  constructor
  · refine ⟨(fun i => if 0 ≤ v i then mf i else mb i, sf, sb), ?_, ?_⟩
    · intro i
      refine ⟨?_, ⟨(hsf i).le, le_rfl⟩, ⟨(hsb i).le, le_rfl⟩⟩
      by_cases h : 0 ≤ v i
      · simp only [h, if_true]; exact ⟨hm i, le_rfl⟩
      · simp only [h, if_false]; exact ⟨le_rfl, hm i⟩
    · simp only [cssBound, fbValue]
      congr 1
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases h : 0 ≤ v i <;> simp [h]
      · congr 2
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases h : 0 ≤ v i
        · have : ¬ v i < 0 := not_lt.mpr h
          simp [h, this]
        · have : v i < 0 := lt_of_not_ge h
          simp [h, this]
  · rintro _ ⟨p, hp, rfl⟩
    simp only [cssBound, fbValue]
    apply add_le_add
    · refine Finset.sum_le_sum (fun i _ => ?_)
      obtain ⟨⟨h1, h2⟩, -, -⟩ := hp i
      by_cases h : 0 ≤ v i
      · simp only [h, if_true]; exact mul_le_mul_of_nonneg_right h2 h
      · simp only [h, if_false]
        exact mul_le_mul_of_nonpos_right h1 (le_of_lt (lt_of_not_ge h))
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ hL
      refine Finset.sum_le_sum (fun i _ => ?_)
      obtain ⟨-, ⟨f0, f1⟩, ⟨b0, b1⟩⟩ := hp i
      by_cases h : 0 ≤ v i
      · have : ¬ v i < 0 := not_lt.mpr h
        simp only [h, this, if_true, if_false]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ f0 f1 2) (sq_nonneg _)
      · have : v i < 0 := lt_of_not_ge h
        simp only [h, this, if_true, if_false]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ b0 b1 2) (sq_nonneg _)
