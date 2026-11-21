-- Prove2me | solution 1 for GRH.sharp_mobius_character_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:13:59.964779+00:00
-- url     : https://prove2.me/submissions/f7b33b31-4083-4dff-b521-3ddfec30b124
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_moebius_partial_sum_reduced_progression_power_bound
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

set_option autoImplicit false

open Filter Asymptotics
open scoped BigOperators

private lemma sharp_progression_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (H : ∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ Finset.range (n+1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
        C * ((n : ℝ) + 1)^σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖∑ k ∈ Finset.range (n+1), χ (k : ZMod q) * (ArithmeticFunction.moebius k : ℂ)‖ ≤
        C * ((n : ℝ) + 1)^σ := by
  classical
  let A (a : ZMod q) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1),
    if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0
  have hterms (a : ZMod q) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖χ a * (A a n : ℂ)‖ ≤ C * ((n : ℝ) + 1)^σ := by
    by_cases ha : IsUnit a
    · obtain ⟨C, hC, hc⟩ := H a ha
      refine ⟨C, hC, fun n => ?_⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact ((mul_le_mul_of_nonneg_right (χ.norm_le_one a) (abs_nonneg (A a n))).trans_eq
        (one_mul _)).trans (hc n)
    · exact ⟨0, le_rfl, fun n => by simp [χ.map_nonunit ha]⟩
  choose C hC hc using hterms
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ => hC a), fun n => ?_⟩
  have heq : ∑ k ∈ Finset.range (n+1), χ (k : ZMod q) * (ArithmeticFunction.moebius k : ℂ) =
      ∑ a, χ a * (A a n : ℂ) := by
    simp only [A, Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_zero,
      Complex.ofReal_intCast, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by simp
  rw [heq, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hc a n)

theorem solution
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    (fun n : ℕ => ∑ k ∈ Finset.range (n+1),
      χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by
  obtain ⟨C, hC, hsum⟩ := sharp_progression_bound q χ σ
    (fun a ha => GRH.moebius_partial_sum_reduced_progression_power_bound q a ha σ hhalf hone)
  refine isBigO_iff.mpr ⟨C * 2 ^ σ, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 ≤ (n : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn₀ _)]
  calc
    _ ≤ C * ((n : ℝ) + 1) ^ σ := hsum n
    _ ≤ C * (2 * (n : ℝ)) ^ σ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn₀, mul_assoc]
