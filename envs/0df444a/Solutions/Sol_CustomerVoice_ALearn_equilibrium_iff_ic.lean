-- Prove2me | solution 1 for CustomerVoice.ALearn.equilibrium_iff_ic
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:09:03.505351+00:00
-- url     : https://prove2.me/submissions/6a6eaeef-ead2-44db-82bc-0d41aaf555a4

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
theorem solution (M : Model) (hM : M.Standing) :
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

#print axioms solution
