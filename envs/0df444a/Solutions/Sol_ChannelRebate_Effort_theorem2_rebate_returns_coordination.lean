-- Prove2me | solution 1 for ChannelRebate.Effort.theorem2_rebate_returns_coordination
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:05:16.806354+00:00
-- url     : https://prove2.me/submissions/90eff984-a407-4fa0-85a1-604ac3d8527b

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting
import Theorems.Thm_ChannelRebate_Effort_theorem2_coordination_of_set
import Theorems.Thm_ChannelRebate_Effort_theorem2_existence

open MeasureTheory Filter Topology

open ChannelRebate.Effort in
theorem solution
    (p c s a : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (Qb : ℝ) (hQb : IsQbar0 p c s Qb)
    (κ : ℝ) (hκ0 : 0 < κ) (hκPi : κ < Lam a (ebarOf p s a Qb)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < κ →
      (∃ w T : ℝ, c < w ∧ w < p ∧
          (∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂) ∧
          IsLlow p c s a w T (κ - ε) ∧ IsLbar p c s a w T κ) ∧
      ∀ w T : ℝ, c < w → w < p →
        (∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂) →
        IsLlow p c s a w T (κ - ε) → IsLbar p c s a w T κ →
          (0 < uT p c s a w T ∧ s < bT p c s a w T ∧ bT p c s a w T < w ∧ 0 < T) ∧
          optimalPairs (R p w (uT p c s a w T) (bT p c s a w T) a T) =
            {(ebarOf p s a Qb * Qb, ebarOf p s a Qb)} ∧
          R p w (uT p c s a w T) (bT p c s a w T) a T
              (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) = κ ∧
          M c s w (uT p c s a w T) (bT p c s a w T) T
              (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) = Lam a (ebarOf p s a Qb) - κ := by
  obtain ⟨ε₀, hε₀, hex⟩ := theorem2_existence p c s a hc hcp hsc ha Qb hQb κ hκ0 hκPi
  exact ⟨ε₀, hε₀, fun ε hε hεε₀ hεκ =>
    ⟨hex ε hε hεε₀ hεκ,
     theorem2_coordination_of_set p c s a hc hcp hsc ha Qb hQb κ hκ0 hκPi ε hε hεκ⟩⟩
