-- Prove2me | solution 1 for CustomerVoice.ALearn.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:09:20.041359+00:00
-- url     : https://prove2.me/submissions/177c8c84-6227-40b9-9115-df7ee9f76b23

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
theorem CustomerResearch.optimal_design (M : Model) (hM : M.Standing) :
    ∀ t : BType,
      (0 ≤ M.qOpt (M.θ t) ∧
        IsMaxOn (fun q : ℝ => M.v q (M.θ t)) (Set.Ici 0) (M.qOpt (M.θ t))) ∧
      ∀ q : ℝ, 0 ≤ q →
        IsMaxOn (fun r : ℝ => M.v r (M.θ t)) (Set.Ici 0) q →
          q = M.qOpt (M.θ t) := by
  intro t
  have ht : 0 < M.θ t := by
    cases t
    · exact hM.θL_pos.trans hM.θH_gt_θL
    · exact hM.θL_pos
  have hs := hM.s_pos
  have hg := hM.γ_pos
  have hk := hM.k_pos
  have hc : 0 < M.s+M.γ*M.k := by positivity
  have hq := (CustomerResearch.design_positive M hM ht).1
  have gap (q : ℝ) : M.v (M.qOpt (M.θ t)) (M.θ t) - M.v q (M.θ t) =
      (M.s+M.γ*M.k)*(q-M.qOpt (M.θ t))^2 := by
    unfold Model.v Model.qOpt
    field_simp
    ring
  have bound (q : ℝ) : M.v q (M.θ t) ≤ M.v (M.qOpt (M.θ t)) (M.θ t) := by
    have := mul_nonneg hc.le (sq_nonneg (q-M.qOpt (M.θ t)))
    rw [← gap q] at this
    linarith
  refine ⟨⟨hq.le, fun q _ => bound q⟩, ?_⟩
  intro q _ hmax
  have hb := hmax hq.le
  change M.v (M.qOpt (M.θ t)) (M.θ t) ≤ M.v q (M.θ t) at hb
  have he := gap q
  have hz : (q-M.qOpt (M.θ t))^2 ≤ 0 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    simp only [mul_zero]
    linarith only [hb,he]
  nlinarith only [hz]



-- Full equilibrium characterization, including arbitrary message relabeling.
theorem CustomerResearch.equilibrium_iff_ic (M : Model) (hM : M.Standing) :
    M.InformativeEq ↔ M.ICH ∧ M.ICL := by
  have hopt := CustomerResearch.optimal_design M hM
  constructor
  · rintro ⟨m,bel,d,hinj,hbel,hsel,hbuy⟩
    have hd (x : Msg) : d x = M.qOpt (M.θ (bel x)) :=
      (hopt (bel x)).2 (d x) (hsel x).1 (hsel x).2
    constructor
    · have h := hbuy BType.H (m BType.L)
      simpa only [hd, hbel, Model.θ, Model.u, Model.ICH] using h
    · have h := hbuy BType.L (m BType.H)
      simpa only [hd, hbel, Model.θ, Model.u, Model.ICL] using h
  · rintro ⟨hH,hL⟩
    let m : BType → Msg | .H => .mH | .L => .mL
    let bel : Msg → BType | .mH => .H | .mL => .L
    refine ⟨m,bel,fun x => M.qOpt (M.θ (bel x)), ?_⟩
    refine ⟨by decide, ?_, ?_, ?_⟩
    · intro t; cases t <;> rfl
    · intro x; exact (hopt (bel x)).1
    · intro t x
      cases t <;> cases x <;>
        simp_all [m,bel,Model.θ,Model.ICH,Model.ICL,Model.u]



-- Alexander Richard Towell (queelius), with Codex assistance.
-- Liang Guo, The Voice of Customers in Customization, SSRN 3994319, §3.2.
theorem CustomerResearch.high_threshold (M : Model) (hM : M.Standing) :
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



-- Alexander Richard Towell (queelius), with Codex assistance.
-- Liang Guo, The Voice of Customers in Customization, SSRN 3994319, §3.2.
theorem CustomerResearch.low_threshold (M : Model) (hM : M.Standing) :
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



-- Full Proposition 1, with the supporting proofs included above.
theorem solution (M : Model) (hM : M.Standing) :
    M.InformativeEq ↔ M.θH / M.θL ≥ M.Delta := by
  rw [CustomerResearch.equilibrium_iff_ic M hM,
    CustomerResearch.high_threshold M hM, CustomerResearch.low_threshold M hM]
  change (M.DeltaH ≤ M.θH/M.θL ∧ M.DeltaL ≤ M.θH/M.θL) ↔
    max M.DeltaH M.DeltaL ≤ M.θH/M.θL
  exact max_le_iff.symm

#print axioms solution
