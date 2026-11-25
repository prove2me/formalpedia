-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.region_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:49:11.352939+00:00
-- url     : https://prove2.me/submissions/7ff68129-886c-4af3-b915-15eebb46cb21

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinish
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_logMT_ge_one
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zFRDirichlet


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
open Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution : ∃ cR : ℝ, 0 < cR ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T c₁ : ℝ)
    (ρ : ℂ), 3 ≤ M → 2 ≤ T → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → 0 < c₁ → c₁ ≤ cR →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → IsLZero χ ρ → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    cR / 2 ≤ (1 - ρ.re) * Real.log ((M : ℝ) * T) := by
  obtain ⟨cR, hcR, hZ⟩ := Formalism.ZeroFreeDirichlet.zFRDirichlet
  refine ⟨cR, hcR, ?_⟩
  intro M _ χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 hc₁ hβ₁ hρ hρim hne
  have hLg1 := logMT_ge_one M T hM hT2
  have hLg0 : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog2M : Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) ≤ Real.log ((M : ℝ) * T) := by
    simp only [Complex.ofReal_im, abs_zero, zero_add]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog2M0 : 0 < Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
    apply Real.log_pos; simp only [Complex.ofReal_im, abs_zero, zero_add]; nlinarith
  have hreg : InRegion cR M (β₁ : ℂ) := by
    unfold InRegion
    have h1 : c₁ / Real.log ((M : ℝ) * T) ≤ cR / Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
      rw [div_le_div_iff₀ hLg0 hlog2M0]
      have h2 := mul_le_mul_of_nonneg_left hlog2M hc₁0.le
      have h3 := mul_le_mul_of_nonneg_right hc₁ hLg0.le
      linarith only [h2, h3]
    rw [Complex.ofReal_re]; linarith only [h1, hβ₁]
  have hLz' : IsLZero χ₁ (β₁ : ℂ) := ⟨Or.inl hχ1ne, hLz⟩
  have hZ1 := (hZ M χ₁ (β₁ : ℂ) hreg hLz').2.2.2.2
  have hnreg : ¬ InRegion cR M ρ := by
    intro h
    obtain ⟨h1, h2⟩ := hZ1 χ ρ h hρ
    exact hne (Prod.ext h1 h2)
  unfold InRegion at hnreg
  push Not at hnreg
  have hlogρ0 : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos; have := abs_nonneg ρ.im; nlinarith
  have hlogρ : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    rw [show (2 : ℝ) * Real.log ((M : ℝ) * T) = Real.log (((M : ℝ) * T) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by have := abs_nonneg ρ.im; positivity)
    have : |ρ.im| + 2 ≤ 2 * T := by linarith
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hMT : (2 : ℝ) ≤ M * T := by nlinarith
    have hMT2 := mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ M * T)
    calc (M : ℝ) * (|ρ.im| + 2) ≤ M * (2 * T) := mul_le_mul_of_nonneg_left this hM0
      _ ≤ _ := by rw [sq]; linarith
  have h1 : cR / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re := by linarith
  rw [div_lt_iff₀ hlogρ0] at h1
  have hδ0 : 0 < 1 - ρ.re := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hlogρ0.le
    linarith
  have := mul_le_mul_of_nonneg_left hlogρ hδ0.le
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
