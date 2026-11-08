-- Prove2me | solution 1 for BlockchainMarketPower.demand_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:14:01.337512+00:00
-- url     : https://prove2.me/submissions/5627b9ea-7358-42fa-9827-9f78e9da41c6

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace Aux_Q01_demand_eq
open BlockchainMarketPower

theorem demandAt_eq (v₀ a : ℝ) (ha : 1 / 2 < a) (q : Bool) (P : ℝ) (hP : 0 ≤ P) :
    demandAt v₀ a q P = 1 / 2 * (if P ≤ 2 * a - 1 then 1 else 0) := by
  have hden : ∀ t sig : Bool, ∑ q : Bool, jointWeight a q t sig = 1 / 4 := by
    intro t sig
    cases sig <;> simp [jointWeight, signalLaw, Fintype.sum_bool] <;> ring
  have hc : ∀ t sig : Bool, condExpectedValue v₀ a t sig =
      v₀ + (if sig = t then 2 * a - 1 else 1 - 2 * a) := by
    intro t sig
    unfold condExpectedValue
    rw [hden]
    cases t <;> cases sig <;> simp [jointWeight, signalLaw, consumerValue, Fintype.sum_bool] <;> ring
  have hcond : ∀ t sig : Bool, (v₀ ≤ condExpectedValue v₀ a t sig - P) ↔
      (sig = t ∧ P ≤ 2 * a - 1) := by
    intro t sig
    rw [hc]
    by_cases hs : sig = t
    · rw [if_pos hs]
      constructor
      · intro h
        exact ⟨hs, by linarith⟩
      · rintro ⟨-, h⟩
        linarith
    · rw [if_neg hs]
      constructor
      · intro h
        exfalso
        linarith
      · rintro ⟨h, -⟩
        exact absurd h hs
  unfold demandAt
  simp only [hcond]
  by_cases hP' : P ≤ 2 * a - 1
  · cases q <;> simp [Fintype.sum_bool, signalLaw, hP'] <;> ring
  · cases q <;> simp [Fintype.sum_bool, signalLaw, hP']

end Aux_Q01_demand_eq

open BlockchainMarketPower in
theorem solution {N : ℕ} (p : Params N) (q : Bool) (P : ℝ) (hP : 0 ≤ P) :
    p.demand .NB q P = 1 / 2 * (if P ≤ 2 * p.α - 1 then 1 else 0) ∧
      p.demand .B q P =
        1 / 2 * (if P ≤ 2 * (p.α + p.δ * (1 - p.α)) - 1 then 1 else 0) := by
  have hα := p.half_lt_α
  have hα1 := p.α_lt_one
  have hδ := p.δ_pos
  have hB : 1 / 2 < p.α + p.δ * (1 - p.α) := by
    have : 0 < p.δ * (1 - p.α) := mul_pos hδ (by linarith)
    linarith
  simp only [Params.demand, Params.accuracy]
  exact ⟨Aux_Q01_demand_eq.demandAt_eq p.v₀ p.α hα q P hP,
    Aux_Q01_demand_eq.demandAt_eq p.v₀ _ hB q P hP⟩
