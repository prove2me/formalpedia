-- Prove2me | solution 1 for EngagementOpt.Misalign.thm_4_1_step_v
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T09:23:21.599538+00:00
-- url     : https://prove2.me/submissions/8563066d-e604-4593-b96c-9b3635efcba1

import Definitions.Def_EngagementOpt_Misalign_Model
set_option autoImplicit false
namespace EngagementOpt.Misalign

lemma ratio_mono {x y : ℝ} (hx : x < 1) (hy : y < 1) (hxy : x ≤ y) :
    x/(1-x) ≤ y/(1-y) := by
  apply (div_le_div_iff₀ (sub_pos.mpr hx) (sub_pos.mpr hy)).mpr
  nlinarith

lemma span_core (ωS ωT : Params) (hS : InOmega ωS) (hT : InOmega ωT)
    (hp : ωT.p ≤ ωS.p) (hgT : gT ωS < gT ωT) : ωS.q < ωT.q := by
  by_contra h
  have hq : ωT.q ≤ ωS.q := le_of_not_gt h
  have hp' := ratio_mono hT.2.1 hS.2.1 hp
  have hq' : 1/(1-ωT.q) ≤ 1/(1-ωS.q) := by
    apply (div_le_div_iff₀ (sub_pos.mpr hT.2.2.2.1) (sub_pos.mpr hS.2.2.2.1)).mpr
    linarith
  unfold gT at hgT
  linarith

lemma participation_value (W : ℝ) (hW : 0 < W) (ω : Params) (h : InOmega ω)
    (hpart : 0 ≤ gS W ω) : W ≤ ω.v := by
  have hd : 0 < 1-ω.q := sub_pos.mpr h.2.2.2.1
  have hp : 0 ≤ ω.p*W/(1-ω.p) := div_nonneg (mul_nonneg h.1 hW.le) (sub_pos.mpr h.2.1).le
  have hv : 0 ≤ (ω.v-W)/(1-ω.q) := by unfold gS at hpart; linarith
  have ht := (le_div_iff₀ hd).mp hv
  linarith

lemma value_core (W : ℝ) (hW : 0 < W) (ωS ωT : Params) (hS : InOmega ωS)
    (hT : InOmega ωT) (hp : ωT.p ≤ ωS.p) (hq : ωS.q < ωT.q)
    (hgS : gS W ωT < gS W ωS) (hpart : 0 ≤ gS W ωT) : ωT.v < ωS.v := by
  by_contra hv
  have hv : ωS.v ≤ ωT.v := le_of_not_gt hv
  have hw := participation_value W hW ωT hT hpart
  have hdS : 0 < 1-ωS.q := sub_pos.mpr hS.2.2.2.1
  have hdT : 0 < 1-ωT.q := sub_pos.mpr hT.2.2.2.1
  have hp' : ωT.p*W/(1-ωT.p) ≤ ωS.p*W/(1-ωS.p) := by
    simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right (ratio_mono hT.2.1 hS.2.1 hp) hW.le
  have hq' : (ωS.v-W)/(1-ωS.q) ≤ (ωT.v-W)/(1-ωT.q) := by
    calc
      _ ≤ (ωT.v-W)/(1-ωS.q) := div_le_div_of_nonneg_right (sub_le_sub_right hv W) hdS.le
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hw) hdT (by linarith)
  unfold gS at hgS
  linarith

lemma root_core (W : ℝ) (hW : 0 < W) (M : Set Params) (hM : ∀ ω ∈ M, InOmega ω)
    (hpos : ∃ ω ∈ M, 0 < gS W ω) (ωS ωT : Params)
    (hS : IsUtilityMaximizer W M ωS) (hT : IsEngagementMaximizer W M ωT)
    (hne : ωS ≠ ωT) (hdisS : gS W ωT < gS W ωS) (hdisT : gT ωS < gT ωT) :
    ωS.p < ωT.p ∨ (ωS.q < ωT.q ∧ ωT.v < ωS.v) := by
  by_cases hp : ωS.p < ωT.p
  · exact Or.inl hp
  · have hp' := le_of_not_gt hp
    have hs := hM ωS hS.1
    have ht := hM ωT hT.1
    have hq := span_core ωS ωT hs ht hp' hdisT
    exact Or.inr ⟨hq,value_core W hW ωS ωT hs ht hp' hq hdisS hT.2.1⟩

end EngagementOpt.Misalign

open EngagementOpt.Misalign

/-- Proof of Theorem 4.1, p. 17: for `ω_S, ω_T ∈ Ω` and `W > 0`, if `p_T ≤ p_S`, `q_T > q_S`,
`g_S(ω_S) > g_S(ω_T)` and `g_S(ω_T) ≥ 0` (the constraint of (4), used implicitly in the step
marked "(q_T > q_S)"), then `v̄_T < v̄_S`. -/
theorem solution (W : ℝ) (hW : 0 < W) (ωS ωT : Params) (hS : InOmega ωS)
    (hT : InOmega ωT) (hp : ωT.p ≤ ωS.p) (hq : ωS.q < ωT.q) (hgS : gS W ωT < gS W ωS)
    (hpart : 0 ≤ gS W ωT) :
    ωT.v < ωS.v := by exact value_core W hW ωS ωT hS hT hp hq hgS hpart


#print axioms solution
