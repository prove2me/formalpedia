-- Prove2me | solution 1 for ConnesRZ.spectral_star_square
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T20:35:10.028456+00:00
-- url     : https://prove2.me/submissions/035ad7cb-3759-4c6d-af96-259d0ea71a9b

import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
import Theorems.Thm_ConnesRZ_explicit_formula

open Complex MeasureTheory ConnesRZ

namespace ConnesRZSpectral

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

lemma isTest_conv {g₁ g₂ : ℝ → ℂ} (h₁ : IsTest g₁) (h₂ : IsTest g₂) :
    IsTest (conv g₁ g₂) := by
  change IsTest (convolution g₁ g₂ (ContinuousLinearMap.mul ℝ ℂ) volume)
  refine ⟨?_, HasCompactSupport.convolution _ h₁.2 h₂.2⟩
  exact HasCompactSupport.contDiff_convolution_right (n := (⊤ : ℕ∞)) _ h₂.2
    (h₁.1.continuous.locallyIntegrable) h₂.1

end ConnesRZSpectral

open ConnesRZSpectral in
/-- The full, unconditionally summable spectral formula for the Weil quadratic form. -/
theorem solution (g : ℝ → ℂ) (hg : IsTest g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
        (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1))))
      (weilDistribution (conv g (starInv g))) := by
  have hs := explicit_formula (conv g (starInv g)) (isTest_conv hg (isTest_starInv hg))
  simpa only [mellinHat_conv_starInv g hg] using hs
