-- Prove2me | solution 1 for CustomReturns.WinWin.returns_identity_2b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:11:36.723207+00:00
-- url     : https://prove2.me/submissions/cc266ac0-858e-416b-88f8-0e4a8cca6408

import Mathlib
import Definitions.Def_CustomReturns_WinWin_Model

open CustomReturns.WinWin

theorem solution (P : Params)
    (hstanding : P.Standing) (hθ : 0 < P.θ) (hβ : P.βc < 1)
    (hregionS : P.rs ≤ P.θ) (hregionC : rbarbar_c P ≤ P.rc)
    (hcase : rSB1 P ≤ P.rs) (hstrict : P.rs < rSB2 P) :
    (1 - P.ms) * QRs2 P + (1 - P.mc) * QRc2 P - (1 - P.ms) * QRs2b P =
      (1 - P.ms) * (rSB2 P - P.rs) * W P /
        (2 * P.ms * (P.ms - (1 - P.βc) * P.mc)) ∧
    ((1 - P.ms) * QRs2 P + (1 - P.mc) * QRc2 P - (1 - P.ms) * QRs2b P < 0 ↔
      W P < 0) := by
  obtain ⟨hb0, hb1, ht0, ht1, hms0, hmsmc, hmc1, hks0, hkskc, hkc1, hrc0, hrc1, hrcrs,
    hmu, hkcmu, hksmu, hkc2, hks2⟩ := hstanding
  simp only [Params.μc, Params.μs] at *
  have hmc0 : 0 < P.mc := lt_of_le_of_lt hms0 hmsmc
  have h1b : 0 < 1 - P.βc := by linarith
  have hD : 0 < P.ms - (1 - P.βc) * P.mc := by
    have : (1 - P.βc) * P.mc ≤ (P.mc + (1 - P.mc) * P.θ) * (1 - P.βc) := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P.mc) ht0) h1b.le]
    linarith
  have hms : 0 < P.ms := by nlinarith
  have h1ms : 0 < 1 - P.ms := by linarith
  have key : (1 - P.ms) * QRs2 P + (1 - P.mc) * QRc2 P - (1 - P.ms) * QRs2b P =
      (1 - P.ms) * (rSB2 P - P.rs) * W P /
        (2 * P.ms * (P.ms - (1 - P.βc) * P.mc)) := by
    simp only [QRs2, QRc2, QRs2b, rSB2, W, Params.μc, Params.μs]
    have e1 : P.ms - (1 - P.βc) * P.mc ≠ 0 := hD.ne'
    have e2 : P.θ ≠ 0 := hθ.ne'
    have e3 : P.mc ≠ 0 := hmc0.ne'
    have e4 : 1 - P.ms ≠ 0 := h1ms.ne'
    have e5 : 1 - P.βc ≠ 0 := h1b.ne'
    have e6 : P.ms ≠ 0 := hms.ne'
    have e7 : P.ms - P.mc + P.mc * P.βc ≠ 0 := by intro h; apply e1; linarith
    have e8 : P.ms - P.mc * (1 - P.βc) ≠ 0 := by intro h; apply e1; linarith
    field_simp
    ring
  refine ⟨key, ?_⟩
  rw [key]
  have hpos : 0 < (1 - P.ms) * (rSB2 P - P.rs) := mul_pos h1ms (by linarith)
  have hden : 0 < 2 * P.ms * (P.ms - (1 - P.βc) * P.mc) := by positivity
  constructor
  · intro h
    by_contra hW
    push Not at hW
    have : 0 ≤ (1 - P.ms) * (rSB2 P - P.rs) * W P /
        (2 * P.ms * (P.ms - (1 - P.βc) * P.mc)) := by positivity
    linarith
  · intro h
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpos h) hden
