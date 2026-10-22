-- Prove2me | solution 1 for DualMoments.RiskPremium.eq_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:42:58.390947+00:00
-- url     : https://prove2.me/submissions/a7529055-3502-43ef-80fb-ff260cf41c25

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model
set_option autoImplicit false
open DualMoments.RiskPremium

theorem ww_valA (h : ℝ → ℝ) (p0 w0 : ℝ) :
    rduValue id h (lotA p0 w0) = (w0 - 1) * (h p0 - h 0) + (w0 + 1) * (h 1 - h p0) := by
  simp [rduValue, Lottery.cum, Lottery.cumBefore, lotA, Finset.sum_filter, Fin.sum_univ_succ]

theorem ww_valB (h : ℝ → ℝ) (p0 w0 ε x : ℝ) :
    rduValue id h (lotB p0 ε w0 x) = (w0 - 1) * (h (p0 - ε) - h 0)
      + (w0 + x) * (h (p0 + ε) - h (p0 - ε)) + (w0 + 1) * (h 1 - h (p0 + ε)) := by
  have e1 : p0 - ε + 2 * ε = p0 + ε := by ring
  have e2 : p0 - ε + (2 * ε + (1 - p0 - ε)) = 1 := by ring
  simp [rduValue, Lottery.cum, Lottery.cumBefore, lotB, Finset.sum_filter, Fin.sum_univ_succ]
  rw [e1, e2]
  ring

theorem solution (h : ℝ → ℝ) (hh : WeightingStanding h) (p0 w0 ε₁ ρ : ℝ) (hf : Feasible p0 ε₁) :
    IsDTPremium h p0 w0 ε₁ ρ ↔
      ρ = ((h p0 - h (p0 - ε₁)) - (h (p0 + ε₁) - h p0)) / (h (p0 + ε₁) - h (p0 - ε₁)) := by
  obtain ⟨hC2, hmaps, h0, h1, hpos⟩ := hh
  obtain ⟨hp0, hp1, hε, hεlt⟩ := hf
  have hεp : ε₁ < p0 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hε1 : ε₁ < 1 - p0 := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hmono : StrictMonoOn h (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · exact hC2.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have := hpos x ⟨hx.1.le, hx.2.le⟩
      rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)] at this
  have hm : h (p0 - ε₁) < h p0 :=
    hmono ⟨by linarith, by linarith⟩ ⟨hp0.le, hp1.le⟩ (by linarith)
  have hp : h p0 < h (p0 + ε₁) :=
    hmono ⟨hp0.le, hp1.le⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hD : 0 < h (p0 + ε₁) - h (p0 - ε₁) := by linarith
  unfold IsDTPremium
  rw [ww_valA, ww_valB, h0, h1]
  constructor
  · rintro ⟨-, -, heq⟩
    rw [eq_div_iff hD.ne']
    nlinarith [heq]
  · intro hρ
    have hρD : ρ * (h (p0 + ε₁) - h (p0 - ε₁)) =
        (h p0 - h (p0 - ε₁)) - (h (p0 + ε₁) - h p0) := by
      rw [hρ]; field_simp
    refine ⟨?_, ?_, ?_⟩
    · by_contra hc
      push_neg at hc
      have : (1 : ℝ) ≤ ρ := by linarith
      nlinarith [mul_le_mul_of_nonneg_right this hD.le]
    · by_contra hc
      push_neg at hc
      have : ρ ≤ -1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_right this hD.le]
    · nlinarith [hρD]
