-- Prove2me | solution 1 for DecentralizedDistribution.FirstBest.fractional_rule_first_best_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:28:59.01697+00:00
-- url     : https://prove2.me/submissions/1dfb8cdb-6479-42d8-8132-713bc780710d

import Mathlib
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_Game

open MeasureTheory

namespace DecentralizedDistribution.FirstBest

theorem aux_frfbe_expectedPayoff_eq {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) (θ : Fin N → ℝ) (Z : Profile N W) (n : Fin N) :
    expectedPayoff sys μ (fractionalRule sys θ) Z n
      = θ n * expectedCentralProfit sys μ Z := by
  unfold expectedPayoff expectedCentralProfit
  have h : (fun D => payoff sys (fractionalRule sys θ) Z D n)
      = fun D => θ n * centralProfit sys Z D := by
    funext D
    simp only [payoff, fractionalRule]
    ring
  rw [h, integral_const_mul]

theorem aux_frfbe_update_nonneg {N W : ℕ} (Z : Profile N W) (hZ : Z.Nonneg)
    (n : Fin N) (z : Position W) (hz : z.Nonneg) :
    Profile.Nonneg (Function.update Z n z) := by
  intro m
  by_cases hm : m = n
  · subst hm
    simpa using hz
  · simpa [Function.update_of_ne hm] using hZ m

end DecentralizedDistribution.FirstBest

open DecentralizedDistribution.FirstBest
open MeasureTheory

theorem solution {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) [IsProbabilityMeasure μ]
    (θ : Fin N → ℝ) (hθ : ∀ n, 0 < θ n ∧ θ n < 1) (hθsum : ∑ n, θ n = 1)
    (Zc : Profile N W) (hZc : IsFirstBest sys μ Zc) :
    IsNashEquilibrium sys μ (fractionalRule sys θ) Zc := by
  refine ⟨hZc.1, fun n z hz => ?_⟩
  rw [aux_frfbe_expectedPayoff_eq, aux_frfbe_expectedPayoff_eq]
  exact mul_le_mul_of_nonneg_left
    (hZc.2 _ (aux_frfbe_update_nonneg Zc hZc.1 n z hz)) (hθ n).1.le
