-- Prove2me | solution 1 for CustomerVoice.ALearn.icl_iff_threshold
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:08:05.010727+00:00
-- url     : https://prove2.me/submissions/069d7397-db3a-4902-b3b0-a84fa7186e86

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

open CustomerVoice.ALearn

namespace CustomerResearch

theorem design_positive (M : Model) (hM : M.Standing) {t : ℝ} (ht : 0 < t) :
    0 < M.qOpt t ∧ M.k * M.qOpt t < t := by
  have hd : 0 < 2*M.s+2*M.γ*M.k := by
    have hs := hM.s_pos
    have hg := hM.γ_pos
    have hk := hM.k_pos
    positivity
  constructor
  · exact div_pos (mul_pos hM.γ_pos ht) hd
  · unfold Model.qOpt
    rw [← mul_div_assoc, div_lt_iff₀ hd]
    have hs := mul_pos hM.s_pos ht
    have hk := mul_pos (mul_pos hM.γ_pos hM.k_pos) ht
    nlinarith

theorem truthful_surplus (M : Model) (hM : M.Standing) {t : ℝ} (ht : 0 < t) :
    0 < t * M.qOpt t - M.k * M.qOpt t ^ 2 := by
  obtain ⟨hq,hk⟩ := design_positive M hM ht
  nlinarith [mul_pos hq (sub_pos.mpr hk)]

end CustomerResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Liang Guo, The Voice of Customers in Customization, SSRN 3994319, §3.2.
theorem solution (M : Model) (hM : M.Standing) :
    M.ICL ↔ M.θH / M.θL ≥ M.DeltaL := by
  change M.ICL ↔ M.DeltaL ≤ M.θH / M.θL
  have hs := hM.s_pos
  have hg := hM.γ_pos
  have hk := hM.k_pos
  have hH : 0 < M.θH := hM.θL_pos.trans hM.θH_gt_θL
  have hD : 0 < 2*M.s+2*M.γ*M.k := by positivity
  have hden : 0 < M.γ*M.k := mul_pos hg hk
  have hqH := (CustomerResearch.design_positive M hM hH).1
  have hsurL := CustomerResearch.truthful_surplus M hM hM.θL_pos
  have hmsg : M.θL * M.qOpt M.θH - M.θH * M.qOpt M.θH ≤ 0 := by
    nlinarith [mul_pos (sub_pos.mpr hM.θH_gt_θL) hqH]
  have hid : (M.θL * M.qOpt M.θL - M.k * M.qOpt M.θL ^ 2) -
      (M.θL * M.qOpt M.θH - M.k * M.qOpt M.θH ^ 2) =
      M.γ * (M.θH-M.θL) *
        (M.γ*M.k*M.θH - (2*M.s+M.γ*M.k)*M.θL) / (2*M.s+2*M.γ*M.k)^2 := by
    unfold Model.qOpt
    field_simp
    ring
  unfold Model.ICL Model.u Model.uA
  rw [max_eq_right hmsg, sub_self, max_self, max_eq_left hsurL.le]
  simp only [mul_zero, zero_add]
  rw [mul_le_mul_iff_right₀ (sub_pos.mpr hM.γ_lt_one), max_le_iff]
  simp only [hsurL.le, and_true]
  rw [← sub_nonneg, hid, le_div_iff₀ (sq_pos_of_pos hD), zero_mul,
    mul_nonneg_iff_of_pos_left (mul_pos hg (sub_pos.mpr hM.θH_gt_θL))]
  rw [Model.DeltaL, div_le_div_iff₀ hden hM.θL_pos]
  constructor <;> intro h <;> nlinarith only [h]

#print axioms solution
