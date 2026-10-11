-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_escape_signed_packet_vanishing_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T14:30:45.00334+00:00
-- url     : https://prove2.me/submissions/193a8434-6442-4f7f-b19b-59699903f6a0

import Theorems.Thm_ConnesGreen_canonical_quartet_escape_mellin_packet_vanishing_tests
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
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
lemma ConnesGreen.actual_zeroMult_reflection (τ : CriticalZeros) :
    zeroMult (reflectedZero τ).1 = zeroMult τ.1 := by
  exact Zeta23.zeta_mult_reflect τ.1 τ.2

lemma ConnesGreen.actual_quadratic_term_norm_bound
    (g : ℝ → ℂ) (hg : IsTest g) (τ : CriticalZeros) :
    ‖(zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ ≤
      ((zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 +
        (zeroMult (reflectedZero τ).1 : ℝ) *
          ‖mellinHat g (reflectedZero τ).1‖ ^ 2) / 2 := by
  rw [mellinHat_conv_starInv g hg τ.1]
  have hm : (0 : ℝ) ≤ zeroMult τ.1 := Nat.cast_nonneg _
  have hs := sq_nonneg (‖mellinHat g τ.1‖ - ‖mellinHat g (mirror τ.1)‖)
  rw [actual_zeroMult_reflection τ]
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_conj, reflectedZero_val]
  change (zeroMult τ.1 : ℝ) *
    (‖mellinHat g τ.1‖ * ‖mellinHat g (mirror τ.1)‖) ≤ _
  have hh : ‖mellinHat g τ.1‖ * ‖mellinHat g (mirror τ.1)‖ ≤
      (‖mellinHat g τ.1‖ ^ 2 + ‖mellinHat g (mirror τ.1)‖ ^ 2) / 2 := by
    nlinarith [hs]
  calc
    _ ≤ (zeroMult τ.1 : ℝ) *
      ((‖mellinHat g τ.1‖ ^ 2 + ‖mellinHat g (mirror τ.1)‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hh hm
    _ = _ := by ring

lemma ConnesGreen.actual_packet_reflection_sum
    (S : Finset CriticalZeros) (hS : ∀ τ ∈ S, reflectedZero τ ∈ S)
    (e : CriticalZeros → ℝ) :
    (∑ τ ∈ S, e (reflectedZero τ)) = ∑ τ ∈ S, e τ := by
  classical
  apply Finset.sum_bij (fun τ _ => reflectedZero τ)
  · exact hS
  · intro a ha b hb hab
    simpa only [reflectedZero_involutive] using congrArg reflectedZero hab
  · intro b hb
    exact ⟨reflectedZero b, hS b hb, reflectedZero_involutive b⟩
  · intro a ha
    rfl

theorem ConnesGreen.actual_packet_absolute_zero_sum_bound
    (g : ℝ → ℂ) (hg : IsTest g)
    (S : Finset CriticalZeros) (hS : ∀ τ ∈ S, reflectedZero τ ∈ S) :
    (∑ τ ∈ S, ‖(zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤
      ∑ τ ∈ S, (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ τ ∈ S, ((zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 +
      (zeroMult (reflectedZero τ).1 : ℝ) * ‖mellinHat g (reflectedZero τ).1‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun τ _ => actual_quadratic_term_norm_bound g hg τ)
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib,
        actual_packet_reflection_sum S hS
          (fun τ => (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2)]
      ring

theorem ConnesGreen.actual_packet_signed_zero_sum_bound
    (g : ℝ → ℂ) (hg : IsTest g)
    (S : Finset CriticalZeros) (hS : ∀ τ ∈ S, reflectedZero τ ∈ S) :
    |(∑ τ ∈ S, (zeroMult τ.1 : ℂ) *
        mellinHat (conv g (starInv g)) τ.1).re| ≤
      ∑ τ ∈ S, (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 := by
  calc
    _ ≤ ‖∑ τ ∈ S, (zeroMult τ.1 : ℂ) *
      mellinHat (conv g (starInv g)) τ.1‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ τ ∈ S, ‖(zeroMult τ.1 : ℂ) *
      mellinHat (conv g (starInv g)) τ.1‖ := norm_sum_le _ _
    _ ≤ _ := actual_packet_absolute_zero_sum_bound g hg S hS
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
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ := canonical_quartet_escape_mellin_packet_vanishing_tests ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  intro hfailure hno
  obtain ⟨δ, hδ, hδ1, hnear⟩ := he hfailure hno
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ε hε
  obtain ⟨r, hr, hr1, hb⟩ := hnear ε hε
  refine ⟨r, hr, hr1, ?_⟩
  intro T hT hcT hTr
  obtain ⟨g, hg, hpacket, hu, ha, hp, hw0, hw⟩ := hb T hT hcT hTr
  have habs := actual_packet_absolute_zero_sum_bound g hg.1 (quartet ρ)
    (quartet_reflection_closed ρ)
  have hsigned := actual_packet_signed_zero_sum_bound g hg.1 (quartet ρ)
    (quartet_reflection_closed ρ)
  exact ⟨g, hg, hpacket, habs.trans_lt hpacket, hsigned.trans_lt hpacket,
    hu, ha, hp, hw0, hw⟩
