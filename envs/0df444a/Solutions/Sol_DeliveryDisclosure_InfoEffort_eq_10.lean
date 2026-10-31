-- Prove2me | solution 1 for DeliveryDisclosure.InfoEffort.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:04:42.979539+00:00
-- url     : https://prove2.me/submissions/4bcc1e54-3bd2-4824-bc3d-d163e840e479

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model
open DeliveryDisclosure.InfoEffort

theorem solution(P : Params) (hP : Standing P) (p t ϕ : ℝ) (hϕ : ϕ ∈ Set.Icc (0 : ℝ) 1)
    (hp : P.c ≤ p) (ht : 0 ≤ t) :
    dem P p t ϕ ≤ Sbar P ϕ * P.Λ := by
  obtain ⟨hΛ, hβr, hβt, hρ, hωY, hc, hb, _⟩ := hP
  unfold dem Sbar
  apply Real.sSup_le
  · rintro l ⟨_, hl⟩
    refine le_trans hl ?_
    rw [mul_comm (Real.sigmoid _) P.Λ]
    apply mul_le_mul_of_nonneg_left _ hΛ.le
    apply Real.sigmoid_le
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    unfold Vdet Vbar
    have hE : 0 < Real.exp (-(P.μ - l) * t) := Real.exp_pos _
    nlinarith [mul_pos (mul_pos hβr hρ) hE, mul_nonneg hβt.le ht]
  · exact mul_nonneg (Real.sigmoid_pos _).le hΛ.le
