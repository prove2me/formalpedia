-- Prove2me | solution 1 for BehrendWindows.exists_large_noRelation
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:59:32.382506+00:00
-- url     : https://prove2.me/submissions/0964972e-bb06-45d6-8ce1-7ee404407456

import Mathlib
import Definitions.Def_BehrendWindows_NoRelation
import Theorems.Thm_BehrendWindows_exists_large_atMostTwoPerAP
import Theorems.Thm_BehrendWindows_noRelation_of_atMostTwoPerAP

open BehrendWindows

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ L n : ℕ, 2 ≤ L → ∃ T : Finset ℤ,
      (∀ s ∈ T, 0 ≤ s ∧ 4 * L * s < n) ∧ NoRelation T L ∧
      ((n : ℝ) / L) * Real.exp (-C * Real.sqrt (Real.log n * Real.log L)) ≤ (T.card : ℝ) := by
  obtain ⟨C₀, hC₀, hgoal⟩ := exists_large_atMostTwoPerAP
  refine ⟨2 * C₀ + 2, by linarith, ?_⟩
  intro L n hL
  obtain ⟨K, hK⟩ : ∃ K, K = 4 * L := ⟨_, rfl⟩
  have hKpos : 0 < K := by omega
  obtain ⟨N', hN'⟩ : ∃ N', N' = (n + K - 1) / K := ⟨_, rfl⟩
  -- `N' = ⌈n / K⌉`
  have hN1 : n ≤ N' * K := by
    have h1 := Nat.div_add_mod (n + K - 1) K
    have h2 := Nat.mod_lt (n + K - 1) hKpos
    rw [← hN'] at h1
    rw [mul_comm]
    generalize K * N' = P at h1 ⊢
    generalize (n + K - 1) % K = r at h1 h2
    omega
  have hN2 : N' * K + 1 ≤ n + K := by
    have := Nat.div_mul_le_self (n + K - 1) K
    rw [← hN'] at this
    omega
  obtain ⟨T, hTsub, hTsp, hTcard⟩ := hgoal N' (2 * L + 1)
  refine ⟨T, ?_, noRelation_of_atMostTwoPerAP hTsp, ?_⟩
  · intro s hs
    have hmem := Finset.mem_Ico.mp (hTsub hs)
    refine ⟨hmem.1, ?_⟩
    have hs' : s + 1 ≤ (N' : ℤ) := by linarith [hmem.2]
    have hN2' : (N' : ℤ) * K + 1 ≤ n + K := by exact_mod_cast hN2
    have hKz : (K : ℤ) = 4 * L := by rw [hK]; push_cast; ring
    have hK0 : (0 : ℤ) ≤ K := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hs' hK0]
  · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; simp
    have hN'1 : 1 ≤ N' := by
      rcases Nat.eq_zero_or_pos N' with h | h
      · rw [h, zero_mul] at hN1; omega
      · exact h
    have hN'pos : (0 : ℝ) < N' := by exact_mod_cast hN'1
    have hcard1 : (1 : ℝ) ≤ T.card := by
      have hB : 0 < (N' : ℝ) * Real.exp (-C₀ * Real.sqrt (Real.log N' * Real.log ((2 * L + 1 : ℕ) : ℝ))) :=
        mul_pos hN'pos (Real.exp_pos _)
      have : 0 < T.card := by exact_mod_cast lt_of_lt_of_le hB hTcard
      exact_mod_cast this
    have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
    have hLpos : (0 : ℝ) < L := by linarith
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- n = 1
      have : n = 1 := by omega
      subst this
      simp only [Nat.cast_one, Real.log_one, zero_mul, Real.sqrt_zero, mul_zero, Real.exp_zero,
        mul_one]
      calc (1 : ℝ) / L ≤ 1 := by rw [div_le_one hLpos]; linarith
        _ ≤ T.card := hcard1
    -- main case `n ≥ 2`
    set x := Real.sqrt (Real.log n * Real.log L) with hxdef
    set y := Real.sqrt (Real.log N' * Real.log ((2 * L + 1 : ℕ) : ℝ)) with hydef
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hLL : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) hLr
    have hx : Real.log 2 ≤ x := by
      calc Real.log 2 = Real.sqrt (Real.log 2 * Real.log 2) := (Real.sqrt_mul_self hlog2.le).symm
        _ ≤ x := Real.sqrt_le_sqrt (mul_le_mul hLn hLL hlog2.le (by linarith))
    have hN'n : N' ≤ n := by
      by_contra hc
      rw [not_le] at hc
      have h1 : (n + 1) * K ≤ N' * K := Nat.mul_le_mul_right K hc
      have h2 : n ≤ n * K := Nat.le_mul_of_pos_right n hKpos
      nlinarith
    have hN'nr : (N' : ℝ) ≤ n := by exact_mod_cast hN'n
    have hN'4 : (n : ℝ) / (4 * L) ≤ N' := by
      rw [div_le_iff₀ (by positivity)]
      have : (n : ℝ) ≤ N' * K := by exact_mod_cast hN1
      have hKr : (K : ℝ) = 4 * L := by rw [hK]; push_cast; ring
      rw [hKr] at this; linarith
    have hlogN' : Real.log N' ≤ Real.log n := Real.log_le_log hN'pos hN'nr
    have hlogN'0 : 0 ≤ Real.log N' := Real.log_nonneg (by exact_mod_cast hN'1)
    have hlog2L : Real.log ((2 * L + 1 : ℕ) : ℝ) ≤ 4 * Real.log L := by
      have e : Real.log ((L : ℝ) ^ 4) = 4 * Real.log L := by rw [Real.log_pow]; norm_num
      rw [← e]
      apply Real.log_le_log (by positivity)
      push_cast
      nlinarith [mul_le_mul hLr hLr (by norm_num) hLpos.le, sq_nonneg ((L : ℝ) ^ 2 - 4)]
    have hlog2L0 : 0 ≤ Real.log ((2 * L + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by push_cast; linarith)
    have hy : y ≤ 2 * x := by
      have hprod : Real.log N' * Real.log ((2 * L + 1 : ℕ) : ℝ) ≤ (2 * x) ^ 2 := by
        rw [mul_pow, hxdef, Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))]
        nlinarith [mul_le_mul hlogN' hlog2L hlog2L0 (by linarith : (0 : ℝ) ≤ Real.log n)]
      calc y ≤ Real.sqrt ((2 * x) ^ 2) := Real.sqrt_le_sqrt hprod
        _ = 2 * x := Real.sqrt_sq (by linarith)
    have hexp1 : Real.exp (-(2 * C₀ + 2) * x) * 4 ≤ Real.exp (-(2 * C₀) * x) := by
      have e : Real.exp (-(2 * C₀ + 2) * x) = Real.exp (-(2 * C₀) * x) * Real.exp (-2 * x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]
      have h4 : Real.exp (-2 * x) * 4 ≤ 1 := by
        have h44 : (4 : ℝ) ≤ Real.exp (2 * x) := by
          have : Real.exp (2 * Real.log 2) = 4 := by
            rw [two_mul, Real.exp_add, Real.exp_log (by norm_num)]; norm_num
          rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
        have e2 : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        nlinarith [Real.exp_pos (-2 * x)]
      nlinarith [Real.exp_pos (-(2 * C₀) * x)]
    have hexp2 : Real.exp (-(2 * C₀) * x) ≤ Real.exp (-C₀ * y) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hy hC₀.le])
    calc (n : ℝ) / L * Real.exp (-(2 * C₀ + 2) * x)
        = (n / (4 * L)) * (Real.exp (-(2 * C₀ + 2) * x) * 4) := by field_simp
      _ ≤ (n / (4 * L)) * Real.exp (-(2 * C₀) * x) :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ ≤ N' * Real.exp (-C₀ * y) := mul_le_mul hN'4 hexp2 (Real.exp_pos _).le hN'pos.le
      _ ≤ T.card := hTcard
