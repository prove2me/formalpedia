-- Prove2me | solution 1 for GDPRDataMarkets.Rights.assumption1_case_i
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:44:22.807995+00:00
-- url     : https://prove2.me/submissions/d7ce783b-ceab-408e-b664-7f1225e3dc8a

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms
open GDPRDataMarkets.Rights

theorem solution(P : Params) (hS : P.Standing) (hA : P.Assumption1) (p1 v : ℝ)
    (hv : vStar P p1 ≤ v) :
    P.kH * v - P.c ≤ 2 * (P.kL * v - P.c) ∧ 0 ≤ P.kH * v - P.c := by
  obtain ⟨hkL, hkLH, hd0, hd1, hc⟩ := hS
  have hσ : 0 < P.sigma := by unfold Params.sigma; linarith
  unfold Params.Assumption1 at hA
  have hA1 : (3 + P.d) * P.sigma ≤ P.mu := le_trans (le_max_left _ _) hA
  unfold vStar at hv
  have h1 : P.c / (P.d * P.sigma) ≤ v := le_trans (le_max_left _ _) hv
  have hds : 0 < P.d * P.sigma := mul_pos hd0 hσ
  have h2 : P.c ≤ P.d * P.sigma * v := by rw [div_le_iff₀ hds] at h1; linarith
  have hv0 : 0 ≤ v := le_trans (div_nonneg hc hds.le) h1
  have hkH : P.kH = P.mu + P.sigma := by unfold Params.mu Params.sigma; ring
  have hkL' : P.kL = P.mu - P.sigma := by unfold Params.mu Params.sigma; ring
  have hσv := mul_nonneg hσ.le hv0
  have e1 := mul_le_mul_of_nonneg_right hA1 hv0
  have e2 := mul_le_mul_of_nonneg_right hd1 hσv
  rw [hkH, hkL']
  constructor <;> nlinarith
