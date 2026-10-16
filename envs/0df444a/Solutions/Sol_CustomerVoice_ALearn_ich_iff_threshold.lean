-- Prove2me | solution 1 for CustomerVoice.ALearn.ich_iff_threshold
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:07:52.577139+00:00
-- url     : https://prove2.me/submissions/0792bd44-f2d3-49d9-9fea-93c6c32d8216

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
    M.ICH ↔ M.θH / M.θL ≥ M.DeltaH := by
  change M.ICH ↔ M.DeltaH ≤ M.θH / M.θL
  have hH : 0 < M.θH := hM.θL_pos.trans hM.θH_gt_θL
  have hD : 0 < 2*M.s+2*M.γ*M.k := by
    have hs := hM.s_pos
    have hg := hM.γ_pos
    have hk := hM.k_pos
    positivity
  have hden : 0 < (1-M.γ)*(2*M.s+M.γ*M.k) := by
    exact mul_pos (sub_pos.mpr hM.γ_lt_one) (by
    have hs := hM.s_pos
    have hg := hM.γ_pos
    have hk := hM.k_pos
    positivity)
  have hqL := (CustomerResearch.design_positive M hM hM.θL_pos).1
  have hsurH := CustomerResearch.truthful_surplus M hM hH
  have hsurL := CustomerResearch.truthful_surplus M hM hM.θL_pos
  have hlie : 0 ≤ M.θH * M.qOpt M.θL - M.k * M.qOpt M.θL ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hM.θH_gt_θL) hqL]
  have hmsg : 0 ≤ M.θH * M.qOpt M.θL - M.θL * M.qOpt M.θL := by
    nlinarith [mul_pos (sub_pos.mpr hM.θH_gt_θL) hqL]
  have hid : M.u M.θH M.θH - M.u M.θH M.θL =
      M.γ * (M.θH-M.θL) *
      ((1-M.γ)*(2*M.s+M.γ*M.k)*M.θH -
        M.γ*(2*M.s+(1+M.γ)*M.k)*M.θL) / (2*M.s+2*M.γ*M.k)^2 := by
    unfold Model.u Model.uA
    rw [sub_self, max_self, max_eq_left hsurH.le, max_eq_left hmsg, max_eq_left hlie]
    unfold Model.qOpt
    field_simp
    ring
  unfold Model.ICH
  rw [← sub_nonneg, hid, le_div_iff₀ (sq_pos_of_pos hD), zero_mul,
    mul_nonneg_iff_of_pos_left (mul_pos hM.γ_pos (sub_pos.mpr hM.θH_gt_θL))]
  rw [Model.DeltaH, div_le_div_iff₀ hden hM.θL_pos]
  constructor <;> intro h <;> nlinarith only [h]

#print axioms solution
