-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_escape_compensated_tail_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T14:46:36.175385+00:00
-- url     : https://prove2.me/submissions/29f501c1-da3f-40a1-8983-df64541a5704

import Theorems.Thm_ConnesGreen_canonical_quartet_escape_signed_packet_vanishing_tests
import Theorems.Thm_ConnesRZ_explicit_formula
import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
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

theorem ConnesGreen.actual_complement_absolute_summable
    (g : ℝ → ℂ) (hg : IsTest g) (S : Finset CriticalZeros) :
    Summable (fun τ : CriticalZeros => ‖if τ ∈ S then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) :=
  (actual_complement_hasSum g hg S).summable.norm

theorem ConnesGreen.actual_complement_restoration_balance
    (g : ℝ → ℂ) (hg : IsTest g) (S : Finset CriticalZeros) (b : ℝ) :
    (∑' τ : CriticalZeros, if τ ∈ S then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re + b =
      (weilDistribution (conv g (starInv g))).re + b -
        (∑ τ ∈ S, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re := by
  rw [(actual_complement_hasSum g hg S).tsum_eq, Complex.sub_re]
  ring
theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
((¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ)) → ¬ (∃ ε : ℝ, 0 < ε ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε) →
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          (∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2) < ε ∧
          (∑ τ ∈ quartet ρ, ‖(zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε ∧
          |(∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| < ε ∧
          HasSum (fun τ : CriticalZeros => if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)
            (weilDistribution (conv g (starInv g)) -
              ∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) ∧
          Summable (fun τ : CriticalZeros => ‖if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
          |(∑' τ : CriticalZeros, if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re +
            ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint
              (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ := canonical_quartet_escape_signed_packet_vanishing_tests ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  intro hfailure hno
  obtain ⟨δ, hδ, hδ1, hnear⟩ := he hfailure hno
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ε hε
  obtain ⟨r, hr, hr1, hb⟩ := hnear (ε / 2) (by linarith)
  refine ⟨r, hr, hr1, ?_⟩
  intro T hT hcT hTr
  obtain ⟨g, hg, hpacket, habs, hsigned, hu, ⟨ha0, ha⟩, ⟨hp0, hp⟩, hw0, hw⟩ := hb T hT hcT hTr
  have hc1 : 0 < c + 1 := by linarith
  have hrest := actual_complement_restoration_balance g hg.1 (quartet ρ)
    (‖(canonicalBackgroundSynthesis (c + 1) hc1 (quartet ρ)).adjoint
      (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)
  have hbounds := abs_lt.mp hsigned
  have hQ : (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalBackgroundSynthesis (c + 1) hc1 (quartet ρ)).adjoint
        (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < 0 := by
    have hprod : 0 < δ * ‖(canonicalSelectedSynthesis (c + 1) hc1 (quartet ρ)).adjoint
      (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 := mul_pos hδ ha0
    linarith
  have hcomp : |(∑' τ : CriticalZeros, if τ ∈ quartet ρ then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re +
      ‖(canonicalBackgroundSynthesis (c + 1) hc1 (quartet ρ)).adjoint
        (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε := by
    rw [hrest]
    apply abs_lt.mpr
    constructor <;> linarith
  refine ⟨g, hg, ?_, ?_, ?_, actual_complement_hasSum g hg.1 (quartet ρ),
    actual_complement_absolute_summable g hg.1 (quartet ρ), hcomp,
    hu, ⟨ha0, ?_⟩, ⟨hp0, ?_⟩, ?_, hw⟩ <;> linarith
