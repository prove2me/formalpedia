-- Prove2me | solution 1 for ConnesGreen.arch_convolution_re_ge_frequency_mass
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T03:36:55.113057+00:00
-- url     : https://prove2.me/submissions/2480e61c-3718-4ca9-83be-c3e93c6fef2b

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib
import Theorems.Thm_ConnesGreen_RG0Integration_critical_mellin_low_mass_fraction
import Theorems.Thm_ConnesGreen_arch_convolution_re_eq_gamma_density
import Theorems.Thm_ConnesGreen_critical_mellin_density_integrable
import Theorems.Thm_ConnesGreen_critical_mellin_mass_identity
import Theorems.Thm_ConnesGreen_gammaBracket_le_of_abs_le
import Theorems.Thm_ConnesGreen_gammaBracket_zero_le
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
import Theorems.Thm_ConnesGreen_mellin_mul_gammaBracket_integrable
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
private noncomputable def gammaSymbol (r : ℝ) : ℝ :=
  (Complex.digamma (1/4 + I*r/2)).re - Real.log Real.pi
private theorem gamma_zero_le (r : ℝ) : gammaSymbol 0 ≤ gammaSymbol r := by
  simpa [gammaSymbol] using ConnesGreen.gammaBracket_zero_le r
lemma conv_eq_convolution (g₁ g₂ : ℝ → ℂ) :
    conv g₁ g₂ = convolution g₁ g₂ (ContinuousLinearMap.mul ℝ ℂ) volume := rfl

/-- The involution `g ↦ g*` preserves test functions. -/
lemma isTest_starInv {g : ℝ → ℂ} (hg : IsTest g) : IsTest (starInv g) := by
  constructor
  · exact Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.contDiff.comp
      (hg.1.comp contDiff_neg)
  · apply HasCompactSupport.intro (K := (fun t : ℝ => -t) '' tsupport g)
      (hg.2.image continuous_neg)
    intro t ht
    have hgt : g (-t) = 0 := by
      by_contra h
      exact ht ⟨-t, subset_tsupport _ h, by simp⟩
    simp [starInv, hgt]

/-- The convolution of two test functions is a test function. -/
lemma isTest_conv {g₁ g₂ : ℝ → ℂ} (h₁ : IsTest g₁) (h₂ : IsTest g₂) :
    IsTest (conv g₁ g₂) := by
  rw [conv_eq_convolution]
  refine ⟨?_, HasCompactSupport.convolution _ h₁.2 h₂.2⟩
  exact HasCompactSupport.contDiff_convolution_right (n := (⊤ : ℕ∞)) _ h₂.2
    (h₁.1.continuous.locallyIntegrable) h₂.1

private theorem critical_square (g : ℝ → ℂ) (hg : IsTest g) (r : ℝ) : mellinHat (conv g (starInv g)) (1 / 2 + I * r) =
    ((‖mellinHat g (1 / 2 + I * r)‖ ^ 2 : ℝ) : ℂ) := by
  rw [ConnesRZ.mellinHat_conv_starInv g hg]
  have he : (1 : ℂ) - (starRingEnd ℂ) (1 / 2 + I * r) = 1 / 2 + I * r := by
    apply Complex.ext <;> simp <;> ring
  rw [he, Complex.mul_conj']
  push_cast
  rfl
theorem solution (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (((Complex.digamma (1/4 + I*B/2)).re - Real.log Real.pi) -
      (((Complex.digamma (1/4 + I*B/2)).re - Real.log Real.pi) - ((Complex.digamma (1/4 : ℂ)).re - Real.log Real.pi)) * (2 * B * T / Real.pi)) *
        (∫ s : ℝ, ‖g s‖ ^ 2) ≤ (archTerm (conv g (starInv g))).re := by
  have hzero : gammaSymbol 0 = (Complex.digamma (1/4 : ℂ)).re - Real.log Real.pi := by simp [gammaSymbol]
  rw [← hzero]
  change (gammaSymbol B - (gammaSymbol B - gammaSymbol 0)*(2*B*T/Real.pi)) *
    (∫ s : ℝ, ‖g s‖^2) ≤ (archTerm (conv g (starInv g))).re

  let d : ℝ → ℝ := fun r => ‖mellinHat g (1 / 2 + I * r)‖ ^ 2
  let l : ℝ → ℝ := (Icc (-B) B).indicator d
  let C := gammaSymbol B - gammaSymbol 0
  have hC : 0 ≤ C := sub_nonneg.mpr (gamma_zero_le B)
  have hd : Integrable d := ConnesGreen.critical_mellin_density_integrable g hg.1
  have hl : Integrable l := hd.indicator measurableSet_Icc
  have hwc := ConnesGreen.mellin_mul_gammaBracket_integrable (conv g (starInv g))
    (isTest_conv hg.1 (isTest_starInv hg.1))
  have hw : Integrable (fun r => d r * gammaSymbol r) := by
    convert hwc.re using 1
    ext r
    rw [critical_square g hg.1,
      ← Complex.ofReal_mul]
    rfl
  have hb : ∀ r, gammaSymbol B * d r - C * l r ≤
      d r * gammaSymbol r := by
    intro r
    by_cases hr : r ∈ Icc (-B) B
    · simp only [l, indicator_of_mem hr]
      have hi := mul_le_mul_of_nonneg_right (gamma_zero_le r) (sq_nonneg ‖mellinHat g (1 / 2 + I * r)‖)
      dsimp [C, d] at *
      nlinarith
    · simp only [l, indicator_of_notMem hr, mul_zero, sub_zero]
      have habs : B ≤ |r| := by
        by_contra hn
        have ha := abs_lt.mp (lt_of_not_ge hn)
        exact hr ⟨ha.1.le, ha.2.le⟩
      have hi := mul_le_mul_of_nonneg_right
        (ConnesGreen.gammaBracket_le_of_abs_le B r hB habs) (sq_nonneg ‖mellinHat g (1 / 2 + I * r)‖)
      simpa [d, gammaSymbol, mul_comm] using hi
  have hi := integral_mono ((hd.const_mul _).sub (hl.const_mul _)) hw hb
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hd.const_mul _) (hl.const_mul _), integral_const_mul,
    integral_const_mul] at hi
  have hmass : (∫ r, d r) = 2 * Real.pi * (∫ s : ℝ, ‖g s‖ ^ 2) :=
    ConnesGreen.critical_mellin_mass_identity g hg.1
  have hlow : (∫ r, l r) ≤ 4 * B * T * (∫ s : ℝ, ‖g s‖ ^ 2) := by
    rw [show (∫ r, l r) = ∫ r in Icc (-B) B, d r from integral_indicator measurableSet_Icc]
    calc
      _ ≤ (2*B*T/Real.pi) * (∫ r : ℝ, ‖mellinHat g (1/2 + I*r)‖^2) :=
        ConnesGreen.RG0Integration.critical_mellin_low_mass_fraction B T hB hT g hg
      _ = _ := by rw [ConnesGreen.critical_mellin_mass_identity g hg.1]; field_simp; ring
  rw [hmass] at hi
  have hhi := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / (2 * Real.pi))
  have hlo := mul_le_mul_of_nonneg_left hlow hC
  rw [ConnesGreen.arch_convolution_re_eq_gamma_density g hg.1]
  change (gammaSymbol B - (gammaSymbol B - gammaSymbol 0)*(2*B*T/Real.pi)) *
    (∫ s : ℝ, ‖g s‖^2) ≤ (1/(2*Real.pi)) *
      ∫ r : ℝ, ‖mellinHat g (1/2 + I*r)‖^2 * gammaSymbol r
  dsimp [d, C] at hhi
  dsimp [C] at hlo
  field_simp at hhi ⊢
  nlinarith [Real.pi_pos]
