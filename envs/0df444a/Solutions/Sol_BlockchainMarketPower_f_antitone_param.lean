-- Prove2me | solution 1 for BlockchainMarketPower.f_antitone_param
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:39:24.355195+00:00
-- url     : https://prove2.me/submissions/ccdb24de-5c4d-4185-a8be-ef11f7264729

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

open BlockchainMarketPower in
theorem solution (P Ψ : ℝ) (hΨ₀ : 0 ≤ Ψ) (hΨ₁ : Ψ ≤ 1) :
    Antitone (fun γ' => BlockchainMarketPower.f P Ψ γ') := by
  intro a b hab
  have hK : 0 ≤ (P - Ψ) ^ 2 * Ψ * (1 - Ψ) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hΨ₀) (sub_nonneg.2 hΨ₁)
  show BlockchainMarketPower.f P Ψ b ≤ BlockchainMarketPower.f P Ψ a
  unfold BlockchainMarketPower.f
  nlinarith [mul_nonneg (sub_nonneg.2 hab) hK]
