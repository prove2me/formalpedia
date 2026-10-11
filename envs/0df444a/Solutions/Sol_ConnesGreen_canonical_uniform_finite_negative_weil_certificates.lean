-- Prove2me | solution 1 for ConnesGreen.canonical_uniform_finite_negative_weil_certificates
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T19:24:37.318251+00:00
-- url     : https://prove2.me/submissions/73441f03-d198-4fc6-ae8a-e9a6a29135ba

import Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_uniform_eventual_arithmetic
import Theorems.Thm_ConnesRZ_explicit_formula
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma ConnesGreen.actual_isTest_starInv {g : ℝ → ℂ} (hg : IsTest g) :
    IsTest (starInv g) := by
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

lemma ConnesGreen.actual_isTest_conv_starInv {g : ℝ → ℂ} (hg : IsTest g) :
    IsTest (conv g (starInv g)) := by
  have hs := actual_isTest_starInv hg
  change IsTest (convolution g (starInv g) (ContinuousLinearMap.mul ℝ ℂ) volume)
  exact ⟨HasCompactSupport.contDiff_convolution_right (n := (⊤ : ℕ∞)) _ hs.2
    (hg.1.continuous.locallyIntegrable) hs.1,
    HasCompactSupport.convolution _ hg.2 hs.2⟩

theorem ConnesGreen.actual_complement_hasSum
    (g : ℝ → ℂ) (hg : IsTest g) (S : Finset CriticalZeros) :
    HasSum (fun τ : CriticalZeros => if τ ∈ S then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)
      (weilDistribution (conv g (starInv g)) -
        ∑ τ ∈ S, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) := by
  classical
  have hfull := ConnesRZ.explicit_formula (conv g (starInv g)) (actual_isTest_conv_starInv hg)
  have hhead : HasSum (fun τ : CriticalZeros => if τ ∈ S then
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1 else 0)
      (∑ τ ∈ S, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) := by
    convert hasSum_sum_of_ne_finset_zero (L := .unconditional CriticalZeros) (s := S)
      (f := fun τ : CriticalZeros => if τ ∈ S then
        (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1 else 0)
      (fun τ hτ => by simp [hτ]) using 1
    simp
  convert hfull.sub hhead using 1 <;> first | rfl | (funext τ; split_ifs <;> simp)

lemma ConnesGreen.actual_finite_real_error_bound
    (g : ℝ → ℂ) (hg : IsTest g) (F : Finset CriticalZeros)
    (hsum : Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖)) :
    |(weilDistribution (conv g (starInv g))).re -
      (∑ τ ∈ F, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| ≤
      ∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
        (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ := by
  have hc := actual_complement_hasSum g hg F
  have hn := norm_tsum_le_tsum_norm hsum
  rw [hc.tsum_eq] at hn
  have he : |(weilDistribution (conv g (starInv g))).re -
      (∑ τ ∈ F, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| ≤
      ‖weilDistribution (conv g (starInv g)) -
        ∑ τ ∈ F, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm
      (weilDistribution (conv g (starInv g)) -
        ∑ τ ∈ F, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1))
  exact he.trans hn

lemma ConnesGreen.negative_iff_robust_finite_margin
    (q : ℝ) (a ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (herr : ∀ n, |q - a n| < ε n) :
    (q < 0 ↔ ∃ n : ℕ, a n < -ε n) ∧
    (q < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n < -ε n) := by
  have hforward : q < 0 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n < -ε n := by
    intro hq
    have hev : ∀ᶠ n in atTop, ε n < -q / 2 :=
      (tendsto_order.mp hε).2 (-q / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, ?_⟩
    intro n hn
    have he := (abs_lt.mp (herr n)).1
    have hh := hN n hn
    linarith
  have hreverse : (∃ n : ℕ, a n < -ε n) → q < 0 := by
    rintro ⟨n, hn⟩
    have he := (abs_lt.mp (herr n)).2
    linarith
  constructor
  · constructor
    · intro hq
      obtain ⟨N, hN⟩ := hforward hq
      exact ⟨N, hN N le_rfl⟩
    · exact hreverse
  · constructor
    · exact hforward
    · rintro ⟨N, hN⟩
      exact hreverse ⟨N, hN N le_rfl⟩
theorem solution
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (K : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hμlim : Tendsto μ atTop (nhds 0)) (hεlim : Tendsto ε atTop (nhds 0)) :
    ∃ F : ℕ → Finset CriticalZeros, Monotone F ∧
      (∀ n, S ⊆ F n ∧ K n ⊆ F n ∧ (∀ τ ∈ F n, reflectedZero τ ∈ F n)) ∧
      (∀ n, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ (F n)}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht (F n)‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht (F n)‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n)) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
          ‖canonicalTailCovariance t ht (F n)‖ < δ ∧
          (∀ ν : ℝ, μ n ≤ ν → ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ < δ) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < δ)) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S))
          atTop (nhds (canonicalPicardMarker t ht S))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T → ∀ δ : ℝ, 0 < δ →
        ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalSupportRightMarker c hc S‖ < δ) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
          ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ g : ℝ → ℂ, SupportedTest t g →
              ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
                ((1 / 2 - η)⁻¹ - 1) * (((weilDistribution (conv g (starInv g))).re) +
                  ‖(canonicalSelectedSynthesis t ht (F n)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
                  μ n * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
          ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∀ g : ℝ → ℂ, SupportedTest t g →
              ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
                ((1 / 2 - η)⁻¹ - 1) * (((weilDistribution (conv g (starInv g))).re) +
                  ‖(canonicalSelectedSynthesis t ht (F n)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
                  μ n * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) ∧
      (∀ n : ℕ, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
          |(weilDistribution (conv g (starInv g))).re - (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| < ε n) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
          (((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ n : ℕ, (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -ε n) ∧
           ((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -ε n))) := by
  obtain ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered, hequiv, hcommon⟩ :=
    canonical_endpoint_half_iff_uniform_eventual_arithmetic T hT S K μ ε hμ hε hε1 hμlim hεlim
  have happrox : ∀ n : ℕ, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
      ∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
        |(weilDistribution (conv g (starInv g))).re - (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| < ε n := by
    intro n t ht htT g hg hx
    obtain ⟨Ptail, hcols, hsmall, hband, hactual⟩ := hstage n t ht htT
    obtain ⟨hsum, hbound⟩ := hactual g hg hx
    exact (actual_finite_real_error_bound g hg.1 (F n) hsum).trans_lt hbound
  refine ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered, hequiv, hcommon, happrox, ?_⟩
  intro t ht htT g hg hx
  exact negative_iff_robust_finite_margin _ _ ε hεlim
    (fun n => happrox n t ht htT g hg hx)
