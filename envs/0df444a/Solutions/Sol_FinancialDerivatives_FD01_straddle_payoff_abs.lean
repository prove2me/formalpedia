-- Prove2me | solution 1 for FinancialDerivatives.FD01.straddle_payoff_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:19:45.634291+00:00
-- url     : https://prove2.me/submissions/85bb268a-6351-4059-8882-3af6886771ef

import Mathlib
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_callValue
import Definitions.Def_fd01_putValue
import Definitions.Def_fd01_spotValue
open Finset
namespace FinancialDerivatives.FD01
theorem S189F_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ)
    (h : ∀ ω, f ω ≤ g ω) : m.price f ≤ m.price g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (m.statePrice_nonneg ω)
theorem S189F_sub {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) :
    m.price f - m.price g = m.price (fun ω => f ω - g ω) := by
  unfold FinitePriceSystem.price; rw [← sum_sub_distrib]; exact sum_congr rfl fun ω _ => by ring
theorem S189F_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (a : ℝ) :
    m.price (fun _ => a) = m.discount * a := by
  unfold FinitePriceSystem.price; rw [← sum_mul, m.statePrice_sum]
theorem S189F_spotK {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) :
    m.spotValue s - m.discount * K = m.price (fun ω => s ω - K) := by
  rw [← S189F_const m K, FinitePriceSystem.spotValue, S189F_sub]
theorem S189F_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f : Ω → ℝ)
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ m.price f :=
  sum_nonneg fun ω _ => mul_nonneg (m.statePrice_nonneg ω) (h ω)

end FinancialDerivatives.FD01

open FinancialDerivatives.FD01 in
theorem solution (s K : ℝ) :
  max (s - K) 0 + max (K - s) 0 = |s - K| := by
  rcases le_total s K with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring
