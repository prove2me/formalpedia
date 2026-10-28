-- Prove2me | solution 1 for BuyXFree.Threshold.q_le_A
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:17:44.157987+00:00
-- url     : https://prove2.me/submissions/87b9b0f4-714e-415e-ab2c-2c86078e041a

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

open BuyXFree.Threshold in
theorem solution (P : Params) (hP : P.Standing) (hq : P.q ≤ 1 / 2)
    (hδ : 2 / (2 + P.lam) ≤ P.δ) :
    P.q ≤ A P := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP
  have hpos : 0 < 2 + P.lam := by linarith
  have hd : 2 ≤ P.δ * (2 + P.lam) := by
    rwa [div_le_iff₀ hpos] at hδ
  have hD : 0 < 1 - P.δ + P.lam * P.q * P.δ := by
    have : 0 ≤ P.lam * P.q * P.δ := by positivity
    linarith
  unfold A
  rw [le_div_iff₀ hD]
  have h9 : 0 ≤ P.lam * P.δ * (1 / 2 - P.q) := mul_nonneg (by positivity) (by linarith)
  have h10 : 0 ≤ P.q * (P.lam * P.δ * (1 / 2 - P.q)) := mul_nonneg h2 h9
  have h11 : 0 ≤ P.q * (P.lam * P.δ - 2 * (1 - P.δ)) := mul_nonneg h2 (by nlinarith)
  nlinarith
