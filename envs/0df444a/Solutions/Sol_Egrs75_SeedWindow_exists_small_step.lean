-- Prove2me | solution 1 for Egrs75.SeedWindow.exists_small_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:35.212995+00:00
-- url     : https://prove2.me/submissions/46e47925-57c5-4189-8889-4a248a154576

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Theorems.Thm_Egrs75_MathlibAPI_irrational_log_div_log


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SeedWindow
open Nat
open Egrs75
namespace Egrs75.SeedWindow
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℕ, 1 ≤ a ∧
      (a : ℝ) * Real.log p - (b : ℝ) * Real.log q ≠ 0 ∧
      |(a : ℝ) * Real.log p - (b : ℝ) * Real.log q| < ε ∧
      ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q < 0 → 1 ≤ b) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  have hM : 0 < Real.log q := Real.log_pos hq1
  set θ : ℝ := Real.log p / Real.log q with hθdef
  have hθpos : 0 < θ := div_pos hL hM
  have hθirr : Irrational θ := MathlibAPI.irrational_log_div_log hp hq hpq
  -- pick n with log q / (n+1) < ε
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (Real.log q / ε)
  set n : ℕ := max n₀ 1 with hndef
  have hnpos : 0 < n := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hsmall : Real.log q / ((n : ℝ) + 1) < ε := by
    have hn0R : Real.log q / ε < (n : ℝ) := by
      simp_all
    have h1 : Real.log q < ε * (n : ℝ) := by
      have := (div_lt_iff₀ hε).mp hn0R
      linarith
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  -- Dirichlet at θ
  obtain ⟨j, k, hk0, _hkn, happ⟩ := Real.exists_int_int_abs_mul_sub_le θ hnpos
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkθ : 0 < (k : ℝ) * θ := mul_pos hkR hθpos
  -- error at most 1/2, so j ≥ 0
  have hhalf : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hj0 : 0 ≤ j := by
    by_contra hneg
    push Not at hneg
    have hjle : j ≤ -1 := by omega
    have hjR : (j : ℝ) ≤ -1 := by exact_mod_cast hjle
    have h1 : (1 : ℝ) ≤ (k : ℝ) * θ - (j : ℝ) := by linarith
    have h2 : (1 : ℝ) ≤ |(k : ℝ) * θ - (j : ℝ)| := le_trans h1 (le_abs_self _)
    linarith [le_trans happ hhalf]
  -- the step
  have hkt : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hk0.le)
  have hjt : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hj0)
  have ha1 : 1 ≤ k.toNat := by omega
  have hδeq : (k.toNat : ℝ) * Real.log p - (j.toNat : ℝ) * Real.log q
      = ((k : ℝ) * θ - (j : ℝ)) * Real.log q := by
    rw [hkt, hjt, hθdef]
    field_simp
  refine ⟨k.toNat, j.toNat, ha1, ?_, ?_, ?_⟩
  · -- nonzero
    rw [hδeq]
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · -- kθ = j ⟹ θ = j/k rational
      have hθval : θ = (j : ℝ) / (k : ℝ) := by
        rw [eq_div_iff (ne_of_gt hkR)]
        linarith
      exact hθirr ⟨(j : ℚ) / (k : ℚ), by rw [hθval]; push_cast; ring⟩
    · exact absurd h2 (ne_of_gt hM)
  · -- |δ| < ε
    rw [hδeq, abs_mul, abs_of_pos hM]
    calc |(k : ℝ) * θ - (j : ℝ)| * Real.log q
        ≤ (1 / ((n : ℝ) + 1)) * Real.log q := by
          exact mul_le_mul_of_nonneg_right happ hM.le
      _ = Real.log q / ((n : ℝ) + 1) := by ring
      _ < ε := hsmall
  · -- δ < 0 ⟹ b ≥ 1
    intro hδ0
    by_contra hb
    have hb0 : j.toNat = 0 := by omega
    rw [hb0] at hδ0
    push_cast at hδ0
    have hposs : 0 < (k.toNat : ℝ) * Real.log p := by
      have h1 : (0 : ℝ) < (k.toNat : ℝ) := by exact_mod_cast ha1
      exact mul_pos h1 hL
    linarith
end Egrs75.SeedWindow
