-- Prove2me | solution 1 for DualMoments.RiskPremium.risk12_moments
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:52:51.205008+00:00
-- url     : https://prove2.me/submissions/1fd27c86-8bec-45f1-818f-3c0b529df720

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model
open DualMoments.RiskPremium

theorem solution(ε₁ ε₂ : ℝ) :
    (risk12 ε₁ ε₂).variance = 2 * ε₁ * ε₂ ^ 2 ∧ (risk12 ε₁ ε₂).maxiance = 2 * ε₁ ^ 2 * ε₂ ∧
      (risk12 ε₁ ε₂).mass = 2 * ε₁ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Lottery.variance, Lottery.maxiance, Lottery.mass, Lottery.mean, Lottery.cum, Lottery.cumBefore, risk12, Fin.sum_univ_two, Finset.sum_filter] <;> ring
