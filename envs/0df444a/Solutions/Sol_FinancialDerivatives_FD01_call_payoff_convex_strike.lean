-- Prove2me | solution 1 for FinancialDerivatives.FD01.call_payoff_convex_strike
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:20:28.190366+00:00
-- url     : https://prove2.me/submissions/e04f6bd0-ced6-4d70-8a22-c71cff29e53f

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
theorem solution (s K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  max (s - (w * K₁ + (1 - w) * K₂)) 0 ≤ w * max (s - K₁) 0 + (1 - w) * max (s - K₂) 0 := by
  have a := le_max_left (s - K₁) 0; have b := le_max_left (s - K₂) 0
  have c := le_max_right (s - K₁) 0; have d := le_max_right (s - K₂) 0
  have h1w : 0 ≤ 1 - w := by linarith
  refine max_le ?_ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left a hw₀, mul_le_mul_of_nonneg_left b h1w]
