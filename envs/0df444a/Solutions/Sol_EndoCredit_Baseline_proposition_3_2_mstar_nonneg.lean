-- Prove2me | solution 1 for EndoCredit.Baseline.proposition_3_2_mstar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:02:34.552771+00:00
-- url     : https://prove2.me/submissions/13dc9f55-ab09-484a-b323-6a107f47155c

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

open EndoCredit.Baseline in
theorem solution (p : Params) (hp : p.Standing) :
    0 ≤ mStar p ∧ mStar p < 1 / rI p := by
  obtain ⟨⟨hsig, hmuI, hsigI, hrho1, hrho2, hgam, hgam1, hrI, hK, hbh, hqa, hIbar⟩, hδ, hδbar⟩ := hp
  have hα : 1 < alphaPlus p := by
    unfold alphaPlus
    simp only []
    rw [lt_div_iff₀ (by positivity)]
    by_cases h : 2 * quadA p + (betaHat p - rI p - quadA p) < 0
    · have := Real.sqrt_nonneg ((betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p)
      linarith
    · push_neg at h
      have : 2 * quadA p + (betaHat p - rI p - quadA p) <
          Real.sqrt ((betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p) := by
        apply (Real.lt_sqrt h).mpr
        nlinarith [mul_pos hqa hrI]
      linarith
  have hα0 : 0 < alphaPlus p := by linarith
  have hW : 0 < 1 - p.gam + alphaPlus p * p.gam := by
    nlinarith [mul_pos hgam (sub_pos.mpr hα)]
  have hCq : 0 < Cq p := by
    unfold Cq
    exact div_pos (mul_pos (mul_pos hK hα0) hgam) (mul_pos hW hbh)
  have hce : 0 < Cq p ^ (1 / (1 - p.gam)) := Real.rpow_pos_of_pos hCq _
  have hQ : 0 < Q p := by unfold Q; exact mul_pos hδ hce
  have hden : 0 < p.gam * K p * (alphaPlus p - 1) := mul_pos (mul_pos hgam hK) (by linarith)
  have hX : 0 < (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) :=
    div_pos hW hden
  constructor
  · have hXQ : (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) * Q p
        ≤ 1 / rI p := by
      unfold Q
      have h1 : (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) *
          (p.delta * Cq p ^ (1 / (1 - p.gam))) ≤
          (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) *
          (deltaBar p * Cq p ^ (1 / (1 - p.gam))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδbar hce.le) hX.le
      have h2 : (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) *
          (deltaBar p * Cq p ^ (1 / (1 - p.gam))) = 1 / rI p := by
        unfold deltaBar
        rw [Real.rpow_neg hCq.le]
        have := hW.ne'; have := hden.ne'; have := hce.ne'; have := hrI.ne'
        have : alphaPlus p - 1 ≠ 0 := by linarith
        have := hgam.ne'; have := hK.ne'
        have hW' : 1 - p.gam + p.gam * alphaPlus p ≠ 0 := by rw [mul_comm]; exact hW.ne'
        field_simp
        try exact div_self hW'
      linarith
    unfold mStar
    linarith
  · unfold mStar
    have := mul_pos hX hQ
    linarith
