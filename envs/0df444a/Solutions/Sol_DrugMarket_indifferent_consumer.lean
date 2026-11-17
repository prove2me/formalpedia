-- Prove2me | solution 1 for DrugMarket.indifferent_consumer
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:06:10.69705+00:00
-- url     : https://prove2.me/submissions/7e3e0e15-1fe9-47ef-a7e4-b417f96f90c7

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem indifferent_consumer (u z t p_a p_b v_a v_b v_r x : ℝ) (ht : 0 < t) (hx : x ∈ Set.Icc (0:ℝ) 1) :
  utilA u z t p_a v_a v_b v_r x = utilB u z t p_b v_a v_b v_r x ↔ x = (1:ℝ)/2 + (p_b - p_a)/(2*t) := by
  obtain ⟨hx0, hx1⟩ := hx
  unfold utilA utilB
  rw [abs_of_nonneg hx0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - x)]
  have ht' : (2 * t) ≠ 0 := by positivity
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

end DrugMarket

open DrugMarket in
theorem solution (u z t p_a p_b v_a v_b v_r x : ℝ) (ht : 0 < t) (hx : x ∈ Set.Icc (0:ℝ) 1) :
  utilA u z t p_a v_a v_b v_r x = utilB u z t p_b v_a v_b v_r x ↔ x = (1:ℝ)/2 + (p_b - p_a)/(2*t) := by
  obtain ⟨hx0, hx1⟩ := hx
  unfold utilA utilB
  rw [abs_of_nonneg hx0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - x)]
  have ht' : (2 * t) ≠ 0 := by positivity
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring
