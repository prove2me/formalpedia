-- Prove2me | solution 1 for BlackScholesModel.call_payoff_integral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:19:55.538449+00:00
-- url     : https://prove2.me/submissions/c50a17d2-5c98-4398-a1ac-e10385954f45

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open MeasureTheory ProbabilityTheory BlackScholesModel

theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    (∫ z, max (terminalPrice S r σ (T - t) z - K) 0 ∂(gaussianReal 0 1))
      = (∫ z in {z | K < terminalPrice S r σ (T - t) z},
          terminalPrice S r σ (T - t) z ∂(gaussianReal 0 1))
        - K * (gaussianReal 0 1).real {z | K < terminalPrice S r σ (T - t) z} := by
  set X : ℝ → ℝ := terminalPrice S r σ (T - t) with hX
  have hXc : Continuous X := by
    rw [hX]; unfold terminalPrice; fun_prop
  have hA : MeasurableSet {z | K < X z} := measurableSet_lt measurable_const hXc.measurable
  have hXint : Integrable X (gaussianReal 0 1) := by
    have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (σ * Real.sqrt (T - t))).const_mul
      (S * Real.exp ((r - σ ^ 2 / 2) * (T - t)))
    refine h.congr (ae_of_all _ (fun z => ?_))
    simp only [hX, terminalPrice]; rw [Real.exp_add]; ring
  have hpt : (fun z => max (X z - K) 0) = {z | K < X z}.indicator (fun z => X z - K) := by
    funext z
    by_cases h : K < X z
    · rw [Set.indicator_of_mem (show z ∈ {z | K < X z} from h), max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (show z ∉ {z | K < X z} from h), max_eq_right (by linarith [not_lt.mp h])]
  rw [hpt, integral_indicator hA, integral_sub hXint.integrableOn (integrable_const K).integrableOn,
    setIntegral_const, smul_eq_mul, mul_comm]
