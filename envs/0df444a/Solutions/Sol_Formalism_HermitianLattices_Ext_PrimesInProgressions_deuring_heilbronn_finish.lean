-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.deuring_heilbronn_finish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:42.038018+00:00
-- url     : https://prove2.me/submissions/aa76c85e-4171-422e-b87a-2e48f7e86e76

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinish
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_logMT_ge_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_region_gap
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : DHFinishOf := by
  intro hT hI
  obtain ⟨cT, AT, BT, hcT, hTur⟩ := hT
  obtain ⟨C, hC, hIneq⟩ := hI
  obtain ⟨cR, hcR, hZ⟩ := DHF.region_gap
  set c : ℝ := min cR (1 / 20) with hc_def
  have hc0 : 0 < c := lt_min hcR (by norm_num)
  have hccR : c ≤ cR := min_le_left _ _
  have hc20 : c ≤ 1 / 20 := min_le_right _ _
  set A : ℕ := max AT 1 with hA_def
  set B : ℕ := max BT 1 with hB_def
  have hA1 : 1 ≤ A := le_max_right _ _
  have hB1 : 1 ≤ B := le_max_right _ _
  set c' : ℝ := min cT (1 / 2) with hc'_def
  have hc'0 : 0 < c' := lt_min hcT (by norm_num)
  have hc'2 : c' ≤ 1 / 2 := min_le_right _ _
  have hTur' : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c' ^ K ≤ (∑ i, z i ^ k).re := by
    intro n K z hn hBn h1 h2 h3
    have hBn' : BT * n ≤ K := le_trans (Nat.mul_le_mul_right _ (le_max_left _ _)) hBn
    obtain ⟨k, hk1, hk2, hk3⟩ := hTur n K z hn hBn' h1 h2 h3
    refine ⟨k, hk1, le_trans hk2 (Nat.mul_le_mul_right _ (le_max_left _ _)), le_trans ?_ hk3⟩
    exact pow_le_pow_left₀ hc'0.le (min_le_left _ _) K
  set q : ℝ := c' / 2 ^ A with hq_def
  have h2A : (2 : ℝ) ≤ 2 ^ A := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ A := pow_le_pow_right₀ (by norm_num) hA1
  have hq0 : 0 < q := by positivity
  have hq4 : q ≤ 1 / 4 := by
    rw [hq_def, div_le_iff₀ (by positivity)]; nlinarith
  set ε : ℝ := q / 4 with hε_def
  have hε0 : 0 < ε := by positivity
  set c₀ : ℝ := q ^ 2 / 200 with hc₀_def
  have hc₀0 : 0 < c₀ := by positivity
  have hc₀s : c₀ ≤ 1 / 3200 := by
    rw [hc₀_def]; have : q ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hq0.le hq4 2
    linarith
  set l : ℝ := -Real.log q with hl_def
  set b : ℝ := 2 * B / ε ^ 2 + 4 with hb_def
  have hb0 : 0 ≤ b := by positivity
  set K0m : ℝ := b + 64 * A * Real.exp (l * b) + 1 with hK0m_def
  have hK0m : 0 < K0m := by positivity
  have hl0 : 0 ≤ l := by
    rw [hl_def]; have := Real.log_nonpos hq0.le (by linarith); linarith
  set c₂ : ℝ := min (c / (2 * K0m)) (ε ^ 2 / (25 * B * C * (2 * l + 2))) with hc₂_def
  have hc₂0 : 0 < c₂ := lt_min (by positivity) (by positivity)
  have hc₂a : c₂ ≤ c / (2 * K0m) := min_le_left _ _
  have hc₂b : c₂ ≤ ε ^ 2 / (25 * B * C * (2 * l + 2)) := min_le_right _ _
  set c₁ : ℝ := c / 2 with hc₁_def
  have hc₁0 : 0 < c₁ := by positivity
  clear_value c A B c' q ε c₀ l b K0m c₂ c₁
  refine ⟨c₀, c₁, c₂, hc₀0, hc₁0, hc₂0, ?_⟩
  intro M _ χ₁ χ β₁ T ρ hM hT2 hχ1sq hχ1ne hLz hβ₁ hβ1 hρ hρre hρim hne
  have hLg1 := DHF.logMT_ge_one M T hM hT2
  set large₂ : ℝ := Real.log ((M : ℝ) * T) with hLg_def
  have hLg0 : 0 < large₂ := by linarith
  set lam : ℝ := 1 - β₁ with hlam_def
  have hlam0 : 0 < lam := by linarith
  have hlamL : lam * large₂ < c₁ := by
    have : lam < c₁ / large₂ := by linarith
    rwa [lt_div_iff₀ hLg0] at this
  have hδL := hZ M χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 (by linarith) hβ₁ hρ hρim hne
  set δ : ℝ := 1 - ρ.re with hδ_def
  have hδL' : c₁ ≤ δ * large₂ := by linarith
  have hδ0 : 0 < δ := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hLg0.le
    linarith
  set K0 : ℝ := Real.log (c₁ / (lam * large₂)) with hK0_def
  have hexpK0 : Real.exp K0 = c₁ / (lam * large₂) := Real.exp_log (by positivity)
  rw [div_le_iff₀ hLg0]
  by_contra hcon
  push Not at hcon
  have hK0big : K0m < K0 := by
    have h1 : c₂ * K0m ≤ c / 2 := by
      calc c₂ * K0m ≤ c / (2 * K0m) * K0m := mul_le_mul_of_nonneg_right hc₂a hK0m.le
        _ = c / 2 := by field_simp
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h hc₂0.le
    linarith
  have hlamη : lam / δ ≤ Real.exp (-K0) := by
    rw [Real.exp_neg, hexpK0, inv_div, div_le_div_iff₀ hδ0 hc₁0]
    have := mul_le_mul_of_nonneg_left hδL' hlam0.le
    linarith
  have hβ20 : 19 / 20 ≤ β₁ := by
    have : c₁ / large₂ ≤ c₁ := div_le_self hc₁0.le hLg1
    linarith
  obtain ⟨N, w, hw, ⟨i0, hi0⟩, -, -, hpow⟩ :=
    hIneq M χ₁ χ β₁ T δ ρ hM hT2 hχ1sq hχ1ne hLz hβ20 hβ1 hρ (by linarith) hρim hne hδ0 (by linarith)
  exact DHF.core c' C A B hc'0 hc'2 hA1 hB1 hC hTur' q ε l b c₂ hq_def hε_def hl_def hb_def hc₂0 hc₂b
    large₂ lam δ K0 (by linarith) hδ0 (by linarith) hlam0 hlamη hcon hLg0 N w hw ⟨i0, hi0⟩ hpow
end Formalism.HermitianLattices.Ext.PrimesInProgressions
