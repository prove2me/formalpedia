-- Prove2me | solution 1 for DualMoments.RiskPremium.risk1_moments
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:52:16.000876+00:00
-- url     : https://prove2.me/submissions/11dd73c9-37ba-416e-97a3-7315a6e7f8a8

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model
open DualMoments.RiskPremium

theorem solution(ε₁ : ℝ) :
    (risk1 ε₁).maxiance = 2 * ε₁ ^ 2 ∧ (risk1 ε₁).mass = 2 * ε₁ := by
  refine ⟨?_, ?_⟩ <;> simp [Lottery.maxiance, Lottery.mass, Lottery.mean, Lottery.cum, Lottery.cumBefore, risk1, Fin.sum_univ_two, Finset.sum_filter] <;> ring
