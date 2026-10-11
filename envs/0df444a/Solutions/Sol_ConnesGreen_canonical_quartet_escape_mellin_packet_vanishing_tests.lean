-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_escape_mellin_packet_vanishing_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T14:04:05.801257+00:00
-- url     : https://prove2.me/submissions/c934d448-ee97-4da0-ac32-6d2861224d54

import Theorems.Thm_ConnesGreen_canonical_quartet_escape_fixed_carrier_neutral_tests
import Theorems.Thm_ConnesGreen_canonical_source_pairing_mellin
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
theorem ConnesGreen.canonical_packet_mellin_energy_bound
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    (∑ τ ∈ S, (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2) ≤
      2 * (‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
        ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2) := by
  classical
  let v := fun τ => sourceEmbed t (actualGreenSource τ)
  let x := sourceEmbed t (problemOneL g)
  have hp := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    ((canonicalPositiveSynthesis t ht).adjoint x) S
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hp
  rw [canonicalPositiveSynthesis] at hp
  simp_rw [columnSynthesis_adjoint_coordinate] at hp
  change (∑ τ ∈ S, ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2) ≤
    ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 at hp
  have hn := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    ((canonicalSelectedSynthesis t ht S).adjoint x) S.attach
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  rw [canonicalSelectedSynthesis] at hn
  simp_rw [columnSynthesis_adjoint_coordinate] at hn
  rw [Finset.sum_attach S (fun τ => ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2)] at hn
  change (∑ τ ∈ S, ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2) ≤
    ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 at hn
  have hpoint : ∀ τ : CriticalZeros,
      (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 ≤
        2 * (‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2 +
          ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2) := by
    intro τ
    have hraw : ‖⟪weightedGreenColumn v τ, x⟫_ℂ‖ ^ 2 =
        (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 := by
      simp only [weightedGreenColumn, Submodule.coe_smul, inner_smul_left]
      change ‖star (Real.sqrt (zeroMult τ.1 : ℝ) : ℂ) *
        ⟪sourceEmbed t (actualGreenSource τ), sourceEmbed t (problemOneL g)⟫_ℂ‖ ^ 2 = _
      rw [canonical_source_pairing_mellin t ht g hg τ, norm_mul, mul_pow]
      simp [Real.sq_sqrt (Nat.cast_nonneg (zeroMult τ.1))]
    have hcol : weightedGreenColumn v τ =
        positiveGreenColumn v τ + negativeGreenColumn v τ := by
      unfold positiveGreenColumn negativeGreenColumn
      module
    have hpair : ⟪weightedGreenColumn v τ, x⟫_ℂ =
        ⟪positiveGreenColumn v τ, x⟫_ℂ + ⟪negativeGreenColumn v τ, x⟫_ℂ := by
      calc
        _ = ⟪positiveGreenColumn v τ + negativeGreenColumn v τ, x⟫_ℂ :=
          congrArg (fun z : Physical t => ⟪z, x⟫_ℂ) hcol
        _ = _ := inner_add_left _ _ _
    have hb := norm_add_le ⟪positiveGreenColumn v τ, x⟫_ℂ ⟪negativeGreenColumn v τ, x⟫_ℂ
    rw [← hpair] at hb
    have h0 := norm_nonneg ⟪weightedGreenColumn v τ, x⟫_ℂ
    have h1 := norm_nonneg ⟪positiveGreenColumn v τ, x⟫_ℂ
    have h2 := norm_nonneg ⟪negativeGreenColumn v τ, x⟫_ℂ
    rw [← hraw]
    nlinarith [sq_nonneg (‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ -
      ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖)]
  have hs := Finset.sum_le_sum (fun τ (_hτ : τ ∈ S) => hpoint τ)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, mul_add] at hs
  change _ ≤ 2 * (∑ τ ∈ S, ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2) +
      2 * (∑ τ ∈ S, ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2) at hs
  dsimp [v, x] at hs
  exact hs.trans (by dsimp [x] at hp hn; nlinarith)
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
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ := canonical_quartet_escape_fixed_carrier_neutral_tests ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  intro hfailure hno
  obtain ⟨δ, hδ, hδ1, hnear⟩ := he hfailure hno
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ε hε
  obtain ⟨r, hr, hr1, hb⟩ := hnear (ε / 4) (by linarith)
  refine ⟨r, hr, hr1, ?_⟩
  intro T hT hcT hTr
  obtain ⟨g, hg, hu, ⟨ha0, ha⟩, ⟨hp0, hp⟩, hw0, hw⟩ := hb T hT hcT hTr
  have hc1 : 0 < c + 1 := by linarith
  have hg1 : SupportedTest (c + 1) g := by
    refine ⟨hg.1, ?_⟩
    intro x hx
    have hs := hg.2 hx
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hpacket := canonical_packet_mellin_energy_bound (c + 1) hc1 (quartet ρ) g hg1
  refine ⟨g, hg, ?_, hu, ⟨ha0, ?_⟩, ⟨hp0, ?_⟩, ?_, hw⟩ <;> linarith
