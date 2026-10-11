-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_escape_absolute_tail_background_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T16:26:15.181802+00:00
-- url     : https://prove2.me/submissions/32cec9a2-b1ec-4175-9369-fd6a45ba8921

import Theorems.Thm_ConnesGreen_canonical_quartet_escape_compensated_tail_tests
import Theorems.Thm_ConnesGreen_canonical_source_pairing_mellin
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
lemma ConnesGreen.tail_zeroMult_reflection (τ : CriticalZeros) :
    zeroMult (reflectedZero τ).1 = zeroMult τ.1 := by
  exact Zeta23.zeta_mult_reflect τ.1 τ.2

lemma ConnesGreen.tail_quadratic_term_norm_bound
    (g : ℝ → ℂ) (hg : IsTest g) (τ : CriticalZeros) :
    ‖(zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ ≤
      ((zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 +
        (zeroMult (reflectedZero τ).1 : ℝ) *
          ‖mellinHat g (reflectedZero τ).1‖ ^ 2) / 2 := by
  rw [mellinHat_conv_starInv g hg τ.1]
  have hm : (0 : ℝ) ≤ zeroMult τ.1 := Nat.cast_nonneg _
  have hs := sq_nonneg (‖mellinHat g τ.1‖ - ‖mellinHat g (mirror τ.1)‖)
  rw [tail_zeroMult_reflection τ]
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


lemma ConnesGreen.tail_weighted_pairing_sq (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (τ : CriticalZeros) :
    ‖⟪weightedGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ,
      sourceEmbed t (problemOneL g)⟫_ℂ‖ ^ 2 =
      (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2 := by
  simp only [weightedGreenColumn, inner_smul_left]
  rw [canonical_source_pairing_mellin t ht g hg τ, norm_mul, mul_pow]
  simp [Real.sq_sqrt (Nat.cast_nonneg (zeroMult τ.1))]

lemma ConnesGreen.actual_zero_term_norm_le_actor_energy (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (τ : CriticalZeros) :
    ‖(zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ ≤
      ‖⟪positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ,
        sourceEmbed t (problemOneL g)⟫_ℂ‖ ^ 2 +
      ‖⟪negativeGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ,
        sourceEmbed t (problemOneL g)⟫_ℂ‖ ^ 2 := by
  let v := fun σ => sourceEmbed t (actualGreenSource σ)
  let x := sourceEmbed t (problemOneL g)
  have hcol : weightedGreenColumn v τ = positiveGreenColumn v τ + negativeGreenColumn v τ := by
    unfold positiveGreenColumn negativeGreenColumn
    module
  have hcolR : weightedGreenColumn v (reflectedZero τ) =
      positiveGreenColumn v τ - negativeGreenColumn v τ := by
    unfold positiveGreenColumn negativeGreenColumn
    module
  have hpair : ⟪weightedGreenColumn v τ, x⟫_ℂ =
      ⟪positiveGreenColumn v τ, x⟫_ℂ + ⟪negativeGreenColumn v τ, x⟫_ℂ := by
    rw [hcol, inner_add_left]
  have hpairR : ⟪weightedGreenColumn v (reflectedZero τ), x⟫_ℂ =
      ⟪positiveGreenColumn v τ, x⟫_ℂ - ⟪negativeGreenColumn v τ, x⟫_ℂ := by
    rw [hcolR, inner_sub_left]
  have hpar := parallelogram_law_with_norm ℂ
    ⟪positiveGreenColumn v τ, x⟫_ℂ ⟪negativeGreenColumn v τ, x⟫_ℂ
  rw [← hpair, ← hpairR] at hpar
  change ‖⟪weightedGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ,
      sourceEmbed t (problemOneL g)⟫_ℂ‖ ^ 2 +
    ‖⟪weightedGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) (reflectedZero τ),
      sourceEmbed t (problemOneL g)⟫_ℂ‖ ^ 2 = _ at hpar
  rw [tail_weighted_pairing_sq t ht g hg τ,
    tail_weighted_pairing_sq t ht g hg (reflectedZero τ)] at hpar
  have hb := tail_quadratic_term_norm_bound g hg.1 τ
  change _ ≤ ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2 +
    ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2
  linarith only [hpar, hb]

theorem ConnesGreen.canonical_absolute_complement_actor_bound
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    Summable (fun τ : CriticalZeros => ‖if τ ∈ S then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
    ((∑' τ : CriticalZeros, ‖if τ ∈ S then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤
      (‖(ContinuousLinearMap.adjoint (canonicalPositiveSynthesis t ht)) (sourceEmbed t (problemOneL g))‖ ^ 2 +
      ‖(ContinuousLinearMap.adjoint (canonicalBackgroundSynthesis t ht S)) (sourceEmbed t (problemOneL g))‖ ^ 2 : ℝ)) := by
  classical
  let v := fun σ => sourceEmbed t (actualGreenSource σ)
  let x := sourceEmbed t (problemOneL g)
  let p := fun τ => ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2
  let n := fun τ => ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2
  have hp : Summable p := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun τ => ?_) ((canonical_actor_columns_summable t ht).1.mul_right (‖x‖ ^ 2))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm (𝕜 := ℂ) (positiveGreenColumn v τ) x) 2
  have hn : Summable n := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun τ => ?_) ((canonical_actor_columns_summable t ht).2.mul_right (‖x‖ ^ 2))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm (𝕜 := ℂ) (negativeGreenColumn v τ) x) 2
  let pc := fun τ => if τ ∈ S then 0 else p τ
  let nc := fun τ => if τ ∈ S then 0 else n τ
  have hpc0 : ∀ τ, 0 ≤ pc τ := by intro τ; dsimp [pc,p]; split_ifs <;> first | exact le_rfl | positivity
  have hnc0 : ∀ τ, 0 ≤ nc τ := by intro τ; dsimp [nc,n]; split_ifs <;> first | exact le_rfl | positivity
  have hpcp : ∀ τ, pc τ ≤ p τ := by intro τ; dsimp [pc,p]; split_ifs <;> first | exact le_rfl | positivity
  have hncn : ∀ τ, nc τ ≤ n τ := by intro τ; dsimp [nc,n]; split_ifs <;> first | exact le_rfl | positivity
  have hpc := Summable.of_nonneg_of_le hpc0 hpcp hp
  have hnc := Summable.of_nonneg_of_le hnc0 hncn hn
  have hbound : ∀ τ : CriticalZeros,
      ‖if τ ∈ S then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ ≤
      pc τ + nc τ := by
    intro τ
    by_cases hτ : τ ∈ S
    · simp [pc,nc,hτ]
    · simpa only [pc,nc,p,n,v,x,if_neg hτ] using
        actual_zero_term_norm_le_actor_energy t ht g hg τ
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hpc.add hnc)
  have hncid : (∑' τ, nc τ) = ∑' τ : {τ : CriticalZeros // τ ∉ S}, n τ.1 := by
    calc
      _ = ∑' τ, ({τ : CriticalZeros | τ ∉ S}).indicator n τ := by
        apply tsum_congr
        intro τ
        by_cases hτ : τ ∈ S <;> simp [nc, Set.indicator, hτ]
      _ = _ := (tsum_subtype {τ : CriticalZeros | τ ∉ S} n).symm
  have hsumBound := hs.tsum_le_tsum hbound (hpc.add hnc)
  have hsumAdd : (∑' τ, (pc τ + nc τ)) = (∑' τ, pc τ) + (∑' τ, nc τ) :=
    hpc.tsum_add hnc
  rw [hsumAdd] at hsumBound
  have hposLe := hpc.tsum_le_tsum hpcp hp
  have htotalBound :
      (∑' τ : CriticalZeros, ‖if τ ∈ S then 0 else
        (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤
      ((∑' τ, p τ) + (∑' τ, nc τ) : ℝ) := by
    linarith only [hsumBound, hposLe]
  have hpId : ‖(ContinuousLinearMap.adjoint (canonicalPositiveSynthesis t ht)) x‖ ^ 2 =
      (∑' τ, p τ) := by
    exact columnSynthesis_adjoint_norm_sq (positiveGreenColumn v)
      (canonical_actor_columns_summable t ht).1 x
  have hbId : ‖(ContinuousLinearMap.adjoint (canonicalBackgroundSynthesis t ht S)) x‖ ^ 2 =
      (∑' τ, nc τ) := by
    rw [hncid]
    exact columnSynthesis_adjoint_norm_sq
      (fun τ : {τ : CriticalZeros // τ ∉ S} => negativeGreenColumn v τ.1)
      ((canonical_actor_columns_summable t ht).2.comp_injective Subtype.val_injective) x
  rw [← hpId, ← hbId] at htotalBound
  exact ⟨hs, htotalBound⟩

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
          |(∑' τ : CriticalZeros, ‖if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) -
            ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint
              (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ := canonical_quartet_escape_compensated_tail_tests ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  intro hfailure hno
  obtain ⟨δ, hδ, hδ1, hnear⟩ := he hfailure hno
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ε hε
  obtain ⟨r, hr, hr1, hb⟩ := hnear (ε / 2) (by linarith)
  refine ⟨r, hr, hr1, ?_⟩
  intro T hT hcT hTr
  obtain ⟨g, hg, hpacket, habs, hsigned, htail, hsum, hcomp, hu,
    ⟨ha0, ha⟩, ⟨hp0, hp⟩, hw0, hw⟩ := hb T hT hcT hTr
  have hc1 : 0 < c + 1 := by linarith
  have hg1 : SupportedTest (c + 1) g := by
    refine ⟨hg.1, ?_⟩
    intro x hx
    have hs := hg.2 hx
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hupper := (canonical_absolute_complement_actor_bound (c + 1) hc1 (quartet ρ) g hg1).2
  have hlower := (Complex.abs_re_le_norm
    (∑' τ : CriticalZeros, if τ ∈ quartet ρ then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)).trans
    (norm_tsum_le_tsum_norm hsum)
  have hneg := neg_le_abs ((∑' τ : CriticalZeros, if τ ∈ quartet ρ then 0 else
    (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re)
  have hcb := (abs_lt.mp hcomp).2
  have hnegN := hneg.trans hlower
  have hN : |(∑' τ : CriticalZeros, ‖if τ ∈ quartet ρ then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) -
      ‖(canonicalBackgroundSynthesis (c + 1) hc1 (quartet ρ)).adjoint
        (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε := by
    apply abs_lt.mpr
    constructor
    · linarith only [hnegN, hcb, hε]
    · linarith only [hupper, hp, hε]
  have hhalf : ε / 2 < ε := by linarith only [hε]
  exact ⟨g, hg, hpacket.trans hhalf, habs.trans hhalf, hsigned.trans hhalf,
    htail, hsum, hcomp.trans hhalf, hN, hu, ⟨ha0, ha.trans hhalf⟩,
    ⟨hp0, hp.trans hhalf⟩, (by linarith only [hw0, hε]), hw⟩
