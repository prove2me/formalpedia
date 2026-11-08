-- Prove2me | solution 1 for DemandResponse.FirstBest.eqA5_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:39:09.756526+00:00
-- url     : https://prove2.me/submissions/a731d61b-20f1-41ab-986f-a4ac9806fae2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model
import Theorems.Thm_DemandResponse_FirstBest_propA3_Vbar_closed_form
import Theorems.Thm_DemandResponse_FirstBest_eqA3_lagrangian_upper_bound
import Theorems.Thm_DemandResponse_FirstBest_eqA4_optimal_contract_attains

open MeasureTheory DemandResponse.FirstBest

theorem solution {N d : ℕ} (P : Params N d) :
    ∃ w : ℝ, w < 0 ∧ Vbar P = (w : EReal) ∧
      VFB P = ((P.R₀ * (w / P.R₀) ^ (1 + P.p / P.r) : ℝ) : EReal) := by
  set w : ℝ := -Real.exp (-rho P * vbarA6 P 0 P.X₀) with hwdef
  have hw : w < 0 := by rw [hwdef]; exact neg_neg_of_pos (Real.exp_pos _)
  have hV : Vbar P = (w : EReal) := propA3_Vbar_closed_form P
  refine ⟨w, hw, hV, ?_⟩
  set f : ℝ → ℝ := fun u => P.R₀ * (u / P.R₀) ^ (1 + P.p / P.r) with hfdef
  have hR := P.hR₀
  have hr := P.hr
  have hp := P.hp
  -- f is monotone on (-∞, 0)
  have hmono : ∀ u v : ℝ, u ≤ v → v < 0 → f u ≤ f v := by
    intro u v huv hv
    simp only [hfdef]
    have h1 : 0 < v / P.R₀ := div_pos_of_neg_of_neg hv hR
    have h2 : v / P.R₀ ≤ u / P.R₀ := div_le_div_of_nonpos_of_le hR.le huv
    have h3 : (v / P.R₀) ^ (1 + P.p / P.r) ≤ (u / P.R₀) ^ (1 + P.p / P.r) :=
      Real.rpow_le_rpow h1.le h2 (by positivity)
    nlinarith
  -- f is continuous at w
  have hcont : ContinuousAt f w := by
    simp only [hfdef]
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.rpow_const (continuousAt_id.div_const _)
    left
    exact (div_pos_of_neg_of_neg hw hR).ne'
  apply le_antisymm
  · -- upper bound
    apply sSup_le
    rintro v ⟨ξ, ν, Q, hξ, hQ, hPC, rfl⟩
    apply eqA3_lagrangian_upper_bound P ξ ν Q hξ hQ hPC w hw
    rw [← hV]
    apply le_sSup
    exact ⟨ν, Q, hQ, rfl⟩
  · -- lower bound
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have hy2' : y < f w := by exact_mod_cast hy2
    -- choose w' < w with f w' > y
    have hev : ∀ᶠ u in nhds w, y < f u := hcont.eventually (lt_mem_nhds hy2')
    obtain ⟨w', hw'1, hw'2⟩ : ∃ w', w' < w ∧ y < f w' := by
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      refine ⟨w - ε / 2, by linarith, hball ?_⟩
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hw'lt : ((w' : ℝ) : EReal) < Vbar P := by rw [hV]; exact_mod_cast hw'1
    obtain ⟨v, ⟨ν, Q, hQ, rfl⟩, hv⟩ := lt_sSup_iff.mp hw'lt
    have hvle : -(((∫⁻ ω, ENNReal.ofReal (Real.exp (-rho P *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω))) ∂Q) : ENNReal) : EReal) ≤ (w : EReal) := by
      rw [← hV]; apply le_sSup; exact ⟨ν, Q, hQ, rfl⟩
    set c := -(((∫⁻ ω, ENNReal.ofReal (Real.exp (-rho P *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω))) ∂Q) : ENNReal) : EReal) with hc
    have hcbot : c ≠ ⊥ := ne_bot_of_gt hv
    have hctop : c ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top w) hvle
    set u := c.toReal with hu
    have hcu : c = (u : EReal) := (EReal.coe_toReal hctop hcbot).symm
    have hu1 : w' < u := by rw [hcu] at hv; exact_mod_cast hv
    have hu2 : u ≤ w := by rw [hcu] at hvle; exact_mod_cast hvle
    have hu0 : u < 0 := lt_of_le_of_lt hu2 hw
    obtain ⟨ξ, hξ, hPC, hJP⟩ := eqA4_optimal_contract_attains P ν Q hQ u hu0 hcu
    have hmem : ((f u : ℝ) : EReal) ≤ VFB P := by
      apply le_sSup
      exact ⟨ξ, ν, Q, hξ, hQ, hPC, hJP.symm⟩
    have hfu : f w' ≤ f u := hmono w' u hu1.le hu0
    have : (y : EReal) < VFB P := by
      calc (y : EReal) < ((f w' : ℝ) : EReal) := by exact_mod_cast hw'2
        _ ≤ ((f u : ℝ) : EReal) := by exact_mod_cast hfu
        _ ≤ VFB P := hmem
    exact absurd hy1 (not_lt.mpr this.le)
