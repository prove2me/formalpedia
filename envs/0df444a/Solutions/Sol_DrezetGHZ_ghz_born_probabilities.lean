-- Prove2me | solution 1 for DrezetGHZ.ghz_born_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:16:52.357455+00:00
-- url     : https://prove2.me/submissions/15593247-f977-429f-8485-cd392ced30f4

import Definitions.Def_DrezetGHZ_Quantum

set_option autoImplicit false
open DrezetGHZ Matrix

set_option maxHeartbeats 800000 in
theorem solution (α β γ : ℤˣ) :
    bornProb .x .x .x α β γ = (if α * β * γ = -1 then 1 / 4 else 0) ∧
    bornProb .x .y .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .x .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .y .x α β γ = (if α * β * γ = 1 then 1 / 4 else 0) := by
  have hs2r : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast hs2r
  have hs4 : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  rcases Int.units_eq_one_or α with rfl | rfl <;>
    rcases Int.units_eq_one_or β with rfl | rfl <;>
    rcases Int.units_eq_one_or γ with rfl | rfl <;>
    norm_num [bornProb, productKet, spinEigenvector, dotProduct, ghzState,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.sq_sqrt] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.normSq_mul, hs4,
      Complex.normSq_ofReal, Real.sq_sqrt]
