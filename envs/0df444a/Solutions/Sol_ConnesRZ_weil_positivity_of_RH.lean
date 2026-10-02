-- Prove2me | solution 1 for ConnesRZ.weil_positivity_of_RH
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-20T02:34:51.67358+00:00
-- url     : https://prove2.me/submissions/adc12c06-e8fa-41b9-af18-d8e71e465c07

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv_critical
import Theorems.Thm_ConnesRZ_explicit_formula

open Complex

open MeasureTheory ConnesRZ

namespace ConnesRZPos

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

end ConnesRZPos

open ConnesRZPos in
theorem solution (hRH : ∀ s : ℂ, IsCriticalZero s → s.re = 1 / 2)
    (g : ℝ → ℂ) (hg : IsTest g) :
    0 ≤ (weilDistribution (conv g (starInv g))).re := by
  have hconv : IsTest (conv g (starInv g)) := isTest_conv hg (isTest_starInv hg)
  have hsum := ConnesRZ.explicit_formula _ hconv
  have hre := Complex.reCLM.hasSum hsum
  refine HasSum.nonneg ?_ hre
  rintro ⟨s, hs⟩
  have hs12 : s = 1 / 2 + I * (s.im : ℝ) := by
    apply Complex.ext <;> simp [hRH s hs]
  have hval : mellinHat (conv g (starInv g)) s = ((‖mellinHat g s‖ ^ 2 : ℝ) : ℂ) := by
    have h := mellinHat_conv_starInv_critical g hg s.im
    rw [← hs12] at h
    exact h
  simp only [Complex.reCLM_apply, hval]
  rw [show ((zeroMult s : ℂ) * ((‖mellinHat g s‖ ^ 2 : ℝ) : ℂ)) =
      (((zeroMult s : ℝ) * ‖mellinHat g s‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re]
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
