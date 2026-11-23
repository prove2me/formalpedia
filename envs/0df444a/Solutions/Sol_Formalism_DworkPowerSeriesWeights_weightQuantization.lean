-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.weightQuantization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:40.20018+00:00
-- url     : https://prove2.me/submissions/8b460c40-afa6-4615-bcd1-3643af2bd6a0

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_succ_dvd_total
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : Quant.{u} := by
  unfold Quant
  intro K _ l d _ hl hd2 hd hl1 hl0 K0 hK0 c hc n hdiv hmono
  have hl2 : 2 ≤ l := hl.two_le
  obtain ⟨m, hm⟩ := succ_dvd_total (f := fun x : V2 d => x.2) (by omega) hd n hdiv
  unfold MonoWtGe at hmono ⊢
  rw [dot_const_wt] at hmono ⊢
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hNm : (∑ x ∈ n.support, (n x : ℝ)) = ((l : ℝ) + 1) * m := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at h
    exact h
  rw [hNm] at hmono ⊢
  by_cases hc0 : c = 0
  · rw [hc0, norm_zero]
    exact Real.rpow_nonneg hl0.le _
  obtain ⟨k, hk⟩ := hK0 c hc hc0
  rw [hk, ← Real.rpow_intCast] at hmono ⊢
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hl0 hl1] at hmono ⊢
  unfold rho at hmono ⊢
  have hL2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hL1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  set ρ := 1 / ((l : ℝ) ^ 2 - 1) with hρ
  set q := 1 / ((l : ℝ) - 1) with hq
  have hρ1 : ρ * ((l : ℝ) ^ 2 - 1) = 1 := by rw [hρ]; exact one_div_mul_cancel hL2.ne'
  have hq1 : q * ((l : ℝ) - 1) = 1 := by rw [hq]; exact one_div_mul_cancel hL1.ne'
  have hq0 : 0 < q := by rw [hq]; exact one_div_pos.mpr hL1
  have e1 : ((l : ℝ) + 1) * ρ = q := by
    rw [hρ, hq, mul_one_div, div_eq_div_iff hL2.ne' hL1.ne']
    ring
  have h1 : 1 - ((l : ℝ) + 1) * m ≤ k * ((l : ℝ) ^ 2 - 1) := by
    have h := mul_le_mul_of_nonneg_right hmono hL2.le
    have e : (ρ - ((l : ℝ) + 1) * m * ρ) * ((l : ℝ) ^ 2 - 1) = 1 - ((l : ℝ) + 1) * m := by
      linear_combination (1 - ((l : ℝ) + 1) * m) * hρ1
    linarith
  have h2 : (1 : ℝ) ≤ ((l : ℝ) + 1) * (k * ((l : ℝ) - 1) + m) := by nlinarith
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = k * ((l : ℤ) - 1) + m := ⟨_, rfl⟩
  have h3 : (1 : ℤ) ≤ ((l : ℤ) + 1) * z := by
    rw [hz]
    exact_mod_cast h2
  have h4 : 1 ≤ z := by
    by_contra hz1
    have hz0 : z ≤ 0 := by omega
    nlinarith
  have h5 : (1 : ℝ) ≤ k * ((l : ℝ) - 1) + m := by
    have h := h4
    rw [hz] at h
    exact_mod_cast h
  have h6 := mul_le_mul_of_nonneg_left h5 hq0.le
  have e2 : q * (k * ((l : ℝ) - 1) + m) = k + q * m := by linear_combination k * hq1
  have e3 : ((l : ℝ) + 1) * m * ρ = q * m := by linear_combination m * e1
  linarith
end Formalism.DworkPowerSeriesWeights
