-- Prove2me | solution 1 for EngagementOpt.Salad.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T11:11:33.976534+00:00
-- url     : https://prove2.me/submissions/c89221e5-5c42-494e-9c3e-1ca6a91558a2

import Definitions.Def_EngagementOpt_Salad_Model
set_option autoImplicit false
namespace SaladResearch
open EngagementOpt.Misalign EngagementOpt.Salad
lemma ratio_id (ω : Params) (h : InOmega ω) : ω.p/(1-ω.p)=aCoef ω-1 := by
  have hd : 1-ω.p≠0 := ne_of_gt (sub_pos.mpr h.2.1)
  dsimp [aCoef]
  field_simp
  <;> ring
lemma duration (ω : Params) (h : InOmega ω) : gT ω=aCoef ω+bCoef ω-1 := by
  unfold gT bCoef
  rw [ratio_id ω h]
  ring
lemma compare_spans (ωS ωT : Params) (hS : InOmega ωS) (hT : InOmega ωT)
    (hgT : gT ωS≤gT ωT) : bCoef ωS-bCoef ωT≤aCoef ωT-aCoef ωS := by
  rw [duration ωS hS,duration ωT hT] at hgT
  linarith
lemma coef_bounds (ω : Params) (hω : InOmega ω) (α : ℝ) (hα : α<1) (hp : ω.p≤α) :
    1≤aCoef ω ∧ aCoef ω≤1/(1-α) := by
  have hd : 0<1-ω.p := sub_pos.mpr hω.2.1
  have ha : 0<1-α := sub_pos.mpr hα
  constructor
  · exact (le_div_iff₀ hd).mpr (by linarith [hω.1])
  · exact (div_le_div_iff₀ hd ha).mpr (by linarith)
lemma utility (W : ℝ) (ω : Params) (h : InOmega ω) :
    gS W ω=bCoef ω*(ω.v-W)-W*(aCoef ω-1) := by
  have hrat := congrArg (fun x : ℝ => W*x) (ratio_id ω h)
  dsimp [gS,bCoef]
  field_simp at hrat ⊢
  <;> nlinarith
lemma gap_identity (W : ℝ) (ωS ωT : Params) (hS : InOmega ωS) (hT : InOmega ωT)
    (hgS : 0≤gS W ωS) (hgT : 0≤gS W ωT) :
    ES W ωS-ES W ωT = bCoef ωS*(ωS.v-ωT.v)+(bCoef ωS-bCoef ωT)*(ωT.v-W)+W*(aCoef ωT-aCoef ωS) := by
  unfold ES
  rw [max_eq_left hgS,max_eq_left hgT,utility W ωS hS,utility W ωT hT]
  ring
lemma participation_value (W : ℝ) (hW : 0<W) (ω : Params) (h : InOmega ω)
    (hpart : 0≤gS W ω) : W≤ω.v := by
  have hd : 0<1-ω.q := sub_pos.mpr h.2.2.2.1
  have hp : 0≤ω.p*W/(1-ω.p) := div_nonneg (mul_nonneg h.1 hW.le) (sub_pos.mpr h.2.1).le
  have hv : 0≤(ω.v-W)/(1-ω.q) := by unfold gS at hpart;linarith
  have ht := (le_div_iff₀ hd).mp hv
  linarith
lemma root_core (W : ℝ) (hW : 0<W) (M : Set Params) (hM : ∀ ω∈M,InOmega ω)
    (hpos : ∃ ω∈M,0<gS W ω) (ωS ωT : Params)
    (hωS : IsUtilityMaximizer W M ωS) (hωT : IsEngagementMaximizer W M ωT)
    (α : ℝ) (hα : α<1) (h1 : ∀ ω∈M,ω.p≤α)
    (v0 β : ℝ) (h2 : ∀ ω∈M,|ω.v-v0|<β) :
    ES W ωT≥ES W ωS-2*β*ET W ωS-α*(v0+β)/(1-α) := by
  have hS := hM ωS hωS.1
  have hT := hM ωT hωT.1
  obtain ⟨ω,hω,hgω⟩ := hpos
  have hgS : 0≤gS W ωS := (hgω.trans_le (hωS.2 hω)).le
  have hgT := hωT.2.1
  have hlen : gT ωS≤gT ωT := hωT.2.2 ⟨hωS.1,hgS⟩
  have hvT := participation_value W hW ωT hT hgT
  have haS := coef_bounds ωS hS α hα (h1 ωS hωS.1)
  have haT := coef_bounds ωT hT α hα (h1 ωT hωT.1)
  have hab : 0≤α := hS.1.trans (h1 ωS hωS.1)
  have hβ : 0<β := (abs_nonneg _).trans_lt (h2 ωS hωS.1)
  have hvS := (abs_lt.mp (h2 ωS hωS.1)).2
  have hvTlo := (abs_lt.mp (h2 ωT hωT.1)).1
  have hvThi := (abs_lt.mp (h2 ωT hωT.1)).2
  have hb : 0≤bCoef ωS := by exact div_nonneg (by norm_num) (sub_pos.mpr hS.2.2.2.1).le
  have hbdur : bCoef ωS≤gT ωS := by rw [duration ωS hS];linarith [haS.1]
  have hspan := compare_spans ωS ωT hS hT hlen
  have hmul1 := mul_le_mul_of_nonneg_left (show ωS.v-ωT.v≤2*β by linarith) hb
  have hmul2 := mul_le_mul_of_nonneg_right hspan (sub_nonneg.mpr hvT)
  have hcoef : aCoef ωT-aCoef ωS≤α/(1-α) := by
    have hid : 1/(1-α)-1=α/(1-α) := by
      have hn : 1-α≠0 := ne_of_gt (sub_pos.mpr hα)
      field_simp
      <;> ring
    rw [←hid]
    linarith [haS.1,haT.2]
  have hmul3 := mul_le_mul_of_nonneg_right hcoef hT.2.2.2.2
  have hmul4 := mul_le_mul_of_nonneg_left (show ωT.v≤v0+β by linarith)
    (div_nonneg hab (sub_pos.mpr hα).le)
  have hmul5 := mul_le_mul_of_nonneg_left hbdur (show 0≤2*β by positivity)
  have hgap := gap_identity W ωS ωT hS hT hgS hgT
  have hET : ET W ωS=gT ωS := by simp [ET,not_lt.mpr hgS]
  rw [hET]
  simp only [div_mul_eq_mul_div] at hmul3 hmul4
  nlinarith only [hmul1,hmul2,hmul3,hmul4,hmul5,hgap]
end SaladResearch

open EngagementOpt.Salad


/-- (5), p. 18, posed with `≤`: if `g_T(ω_T) ≥ g_T(ω_S)` for two points of `Ω`, then
`b_S − b_T ≤ a_T − a_S`. -/
theorem solution (ωS ωT : EngagementOpt.Misalign.Params) (hS : EngagementOpt.Misalign.InOmega ωS) (hT : EngagementOpt.Misalign.InOmega ωT)
    (hgT : EngagementOpt.Misalign.gT ωS ≤ EngagementOpt.Misalign.gT ωT) :
    bCoef ωS - bCoef ωT ≤ aCoef ωT - aCoef ωS := by exact SaladResearch.compare_spans ωS ωT hS hT hgT



#print axioms solution
