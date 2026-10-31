-- Prove2me | solution 1 for BundledPay.Base.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:01:19.652444+00:00
-- url     : https://prove2.me/submissions/c4199492-76d0-47a6-a4f9-96614b937f1b

import Mathlib
import Definitions.Def_BundledPay_Base_Model
open BundledPay.Base

theorem solution(P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (ih ip : ℝ) (hF : IsNashFFS P ih ip) :
    intensity P ih ip =
      if P.psi ≤ psiBar P then P.I0 + P.drp / (2 * P.wb)
      else 1 - P.psi := by
  obtain ⟨h1, h2, hwb, hI0, hI1, hps0, hps1⟩ := hS
  obtain ⟨⟨hih0, hih1⟩, ⟨hip0, hip1⟩, hH, hPh⟩ := hF
  have hh := hH 1 ⟨by norm_num, le_rfl⟩
  simp only [hospFFS, intensity, hwq, zero_mul, sub_zero] at hh
  have hih : ih = 1 := by
    by_contra hne
    have : ih < 1 := lt_of_le_of_ne hih1 hne
    nlinarith [mul_pos (mul_pos (sub_pos.2 h1) (sub_pos.2 this)) hps0]
  subst hih
  have hps1' : 0 < 1 - P.psi := by linarith
  have hdr : P.r1p - P.r2p = 2 * P.wb * (P.drp / (2 * P.wb)) := by
    unfold Params.drp; field_simp
  have hdpos : 0 < P.drp / (2 * P.wb) := div_pos (by unfold Params.drp; linarith) (by linarith)
  unfold psiBar
  set d := P.drp / (2 * P.wb) with hd_def
  simp only [intensity, sub_self, zero_mul, zero_add]
  have hII : (1 - P.psi) * ip ≤ 1 - P.psi := mul_le_of_le_one_right hps1'.le hip1
  have hI0' : 0 ≤ (1 - P.psi) * ip := mul_nonneg hps1'.le hip0
  split_ifs with hc
  · have hT : P.I0 + d ≤ 1 - P.psi := by linarith
    have hdev := hPh ((P.I0 + d) / (1 - P.psi))
      ⟨div_nonneg (by linarith) hps1'.le, (div_le_one hps1').2 hT⟩
    simp only [physFFS, intensity, sub_self, zero_mul, zero_add] at hdev
    rw [show (1 - P.psi) * ((P.I0 + d) / (1 - P.psi)) = P.I0 + d by field_simp] at hdev
    set I := (1 - P.psi) * ip with hI
    have e : (P.r1p * (P.I0 + d) + P.r2p * (1 - (P.I0 + d)) - P.wb * (P.I0 + d - P.I0) ^ 2)
        - (P.r1p * I + P.r2p * (1 - I) - P.wb * (I - P.I0) ^ 2)
        = P.wb * (I - P.I0 - d) ^ 2 := by
      linear_combination (P.I0 + d - I) * hdr
    have hs : P.wb * (I - P.I0 - d) ^ 2 ≤ 0 := by linarith
    have hz : (I - P.I0 - d) ^ 2 = 0 := by
      by_contra hne
      have : 0 < (I - P.I0 - d) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      nlinarith [mul_pos hwb this]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hz
    linarith
  · push_neg at hc
    have hdev := hPh 1 ⟨by norm_num, le_rfl⟩
    simp only [physFFS, intensity, sub_self, zero_mul, zero_add, mul_one] at hdev
    set I := (1 - P.psi) * ip with hI
    have e : (P.r1p * (1 - P.psi) + P.r2p * (1 - (1 - P.psi)) - P.wb * ((1 - P.psi) - P.I0) ^ 2)
        - (P.r1p * I + P.r2p * (1 - I) - P.wb * (I - P.I0) ^ 2)
        = ((1 - P.psi) - I) * (P.wb * (2 * d - ((1 - P.psi) - P.I0) - (I - P.I0))) := by
      linear_combination ((1 - P.psi) - I) * hdr
    have hpos : 0 < P.wb * (2 * d - ((1 - P.psi) - P.I0) - (I - P.I0)) :=
      mul_pos hwb (by linarith)
    have hn : ((1 - P.psi) - I) * (P.wb * (2 * d - ((1 - P.psi) - P.I0) - (I - P.I0))) ≤ 0 := by
      linarith
    by_contra hne
    have hlt : 0 < (1 - P.psi) - I := by
      rcases lt_or_eq_of_le hII with h | h
      · linarith
      · exact absurd h hne
    nlinarith [mul_pos hlt hpos]
