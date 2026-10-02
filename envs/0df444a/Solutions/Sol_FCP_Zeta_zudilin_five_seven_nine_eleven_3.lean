-- Prove2me | solution 3 for FCP.Zeta.zudilin_five_seven_nine_eleven
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T18:21:36.408072+00:00
-- url     : https://prove2.me/submissions/ef2e9663-52e2-4aa8-9a8b-70d8ed7e2afb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZudilinZeta_zudilin_numeric_C1_upper_bound
import Theorems.Thm_ZudilinZeta_exists_saddle_root_params13
import Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_bounds
import Theorems.Thm_ZudilinZeta_zudilin_lemma3
import Theorems.Thm_ZudilinZeta_zetaR_eq_riemannZeta

set_option autoImplicit false

open ZudilinZeta

lemma zudilin_root_from_C1_upper (hC1 : C1 params13<227.5) :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a=x}).Nonempty := by
  obtain ⟨τ, hroot, him, hmax, hre, hpi⟩ := exists_saddle_root_params13
  have hC0 := (zudilin_numeric_C0_bounds τ hroot him hmax).1
  have hC : C1 params13<C0 params13 τ := by linarith only [hC0, hC1]
  obtain ⟨k, hk, hI⟩ := zudilin_lemma3 params13 rfl τ hroot him hmax hre hpi hC
  have hk' : 1≤k ∧ k≤4 := by simpa [Finset.mem_Icc, params13] using hk
  obtain ⟨hklo, hkhi⟩ := hk'
  have hI' : Irrational (zetaR (3+2*k)) := by simpa [params13] using hI
  refine ⟨3+2*k, ?_, ?_⟩
  · interval_cases k <;> norm_num
  · exact ⟨zetaR (3+2*k), hI', zetaR_eq_riemannZeta (3+2*k) (by omega)⟩

theorem solution :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a=x}).Nonempty := by
  exact zudilin_root_from_C1_upper zudilin_numeric_C1_upper_bound
