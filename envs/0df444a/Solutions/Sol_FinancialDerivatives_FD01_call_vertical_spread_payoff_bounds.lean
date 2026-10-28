-- Prove2me | solution 1 for FinancialDerivatives.FD01.call_vertical_spread_payoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:19:36.844167+00:00
-- url     : https://prove2.me/submissions/4941fb92-a472-4fec-b131-0a7edf0f985e

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
theorem solution (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ max (s - K₁) 0 - max (s - K₂) 0 ∧ max (s - K₁) 0 - max (s - K₂) 0 ≤ K₂ - K₁ := by
  have h1 : max (s - K₂) 0 ≤ max (s - K₁) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (s - K₁) 0 ≤ max (s - K₂) 0 + (K₂ - K₁) :=
    max_le (by linarith [le_max_left (s - K₂) 0]) (by linarith [le_max_right (s - K₂) 0])
  constructor <;> linarith
