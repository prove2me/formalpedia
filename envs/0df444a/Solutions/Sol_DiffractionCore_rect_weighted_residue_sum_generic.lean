-- Prove2me | solution 1 for DiffractionCore.rect_weighted_residue_sum_generic
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:58:08.914016+00:00
-- url     : https://prove2.me/submissions/d8a5fba5-174f-4c59-90eb-36b6f943f35c

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_DiffractionCore_rect_weighted_pole_generic

/-  DIFFRACTION CORE (Dyson/quasicrystal axis, QC2 brick 1): the WEIGHTED rectangle pole formula.

    The T-ladder counts zeros (`rect_winding_generic`: `Bd((·-ρ)⁻¹) = 2πi`, the `g ≡ 1` case).
    The Dyson/Weil axis needs WEIGHTED sums over zeros — `Σ_ρ g(ρ)` for analytic test weights —
    because the explicit formula IS the diffraction identity: weighted zero-sums on one side,
    Bragg peaks at `k·log p` (prime sums) on the other.  This brick proves the single-pole
    mechanism over a rectangle:

      `Bd(g·(·-ρ)⁻¹) = 2πi·g(ρ)`   (g holomorphic near the closed box, ρ strictly interior).

    Proof: the removable-singularity split `g(z)·(z-ρ)⁻¹ = dslope g ρ z + g(ρ)·(z-ρ)⁻¹` (off ρ);
    `dslope g ρ` is holomorphic ACROSS ρ (Mathlib `has_fpower_series_dslope_fslope`), so its
    boundary integral vanishes by the generic rectangle Goursat (`rect_arg_principle_generic`);
    the remainder is `g(ρ)` times the counting winding (`rect_winding_generic`).

    Downstream (QC ladder): QC2 brick 2 = finite-sum version over a zero Finset (mirrors
    `box_residue_sum_generic`); QC3 = the finite-height Guinand–Weil identity, pushing the
    right edge to `Re > 1` where Mathlib's `LSeries_vonMangoldt_eq` (`L Λ = -ζ'/ζ`) turns the
    contour into PRIME SUMS — the Bragg peaks, kernel-side.  The Archimedean term is already
    built (`ZeroFreeBridge.logDeriv_gammaR`, the θ-bridge).

    conjecture1_proved = False. -/






open Complex MeasureTheory Real
open scoped Topology

section
namespace DiffractionCore
end DiffractionCore
open DiffractionCore






theorem solution
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    {s : Finset ℂ} (m : ℂ → ℤ) {U : Set ℂ} (g : ℂ → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hsub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U)
    (hin : ∀ ρ ∈ s, sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹))
      - (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹))
      + I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹))
      - I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹))
    = 2 * ↑π * I * ∑ ρ ∈ s, (m ρ : ℂ) * g ρ := by
  have hgcont : ContinuousOn g (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hg.mono hsub).continuousOn
  have hmem_h : ∀ (c : ℝ), c ∈ Set.Icc T0 T1 →
      Set.MapsTo (fun t : ℝ => ((t : ℂ) + (c : ℂ) * I))
        (Set.uIcc sigma0 sigma1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro c hc t ht
    rw [Set.uIcc_of_le hsig] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ht, by simpa using hc⟩
  have hmem_v : ∀ (c : ℝ), c ∈ Set.Icc sigma0 sigma1 →
      Set.MapsTo (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I))
        (Set.uIcc T0 T1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro c hc t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using hc, by simpa using ht⟩
  -- Edge-specific integrability of each summand (pole avoidance from strict interiority).
  have hb : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => (m ρ : ℂ)
      * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)) volume sigma0 sigma1 := by
    intro ρ hρ
    obtain ⟨_, _, h3, _⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h T0 ⟨le_refl _, hT⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at him
    linarith [h3, him]
  have ht : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => (m ρ : ℂ)
      * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)) volume sigma0 sigma1 := by
    intro ρ hρ
    obtain ⟨_, _, _, h4⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h T1 ⟨hT, le_refl _⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at him
    linarith [h4, him]
  have hr : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (m ρ : ℂ)
      * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)) volume T0 T1 := by
    intro ρ hρ
    obtain ⟨_, h2, _, _⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v sigma1 ⟨hsig, le_refl _⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at hre
    linarith [h2, hre]
  have hl : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => (m ρ : ℂ)
      * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)) volume T0 T1 := by
    intro ρ hρ
    obtain ⟨h1, _, _, _⟩ := hin ρ hρ
    refine (ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v sigma0 ⟨le_refl _, hsig⟩))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => ?_))))).const_mul _
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero] at hre
    linarith [h1, hre]
  rw [intervalIntegral.integral_finsetSum (fun ρ hρ => hb ρ hρ),
    intervalIntegral.integral_finsetSum (fun ρ hρ => ht ρ hρ),
    intervalIntegral.integral_finsetSum (fun ρ hρ => hr ρ hρ),
    intervalIntegral.integral_finsetSum (fun ρ hρ => hl ρ hρ)]
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨h1, h2, h3, h4⟩ := hin ρ hρ
  have hW := rect_weighted_pole_generic sigma0 sigma1 T0 T1 ρ g hU hg hsub h1 h2 h3 h4
  simp only [smul_eq_mul] at hW
  linear_combination (m ρ : ℂ) * hW
