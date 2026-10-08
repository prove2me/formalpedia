-- Prove2me | solution 1 for ConnesGreen.canonical_signed_actor_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T04:54:13.746987+00:00
-- url     : https://prove2.me/submissions/08aae6bb-c5e4-4a28-a0f6-87287f64951a

import Theorems.Thm_ConnesGreen_canonical_source_pairing_mellin
import Theorems.Thm_ConnesRZ_explicit_formula
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
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

private theorem mult_reflect (ρ : CriticalZeros) : zeroMult (reflectedZero ρ).1 = zeroMult ρ.1 := by
  exact Zeta23.zeta_mult_reflect ρ.1 ρ.2
private theorem weighted_pairing (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ) (hg : SupportedTest T g) (ρ : CriticalZeros) :
    ⟪weightedGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ =
      (Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) * mellinHat g ρ.1 := by
  simp only [weightedGreenColumn, inner_smul_left, RCLike.conj_ofReal, smul_eq_mul]
  rw [canonical_source_pairing_mellin T hT g hg ρ]
  simp
private theorem signed_pairing (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ) (hg : SupportedTest T g) (ρ : CriticalZeros) :
    ‖⟪positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ‖ ^ 2 -
    ‖⟪negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ‖ ^ 2 =
      (((zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 * star (mellinHat g (mirror ρ.1))))).re := by
  let a := (Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) * mellinHat g ρ.1
  let b := (Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) * mellinHat g (mirror ρ.1)
  have he : ‖(a + b) / 2‖ ^ 2 - ‖(a - b) / 2‖ ^ 2 = (a * star b).re := by
    simp only [norm_div, Complex.norm_ofNat, div_pow, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hp : ⟪positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ = (a+b)/2 := by
    unfold positiveGreenColumn
    rw [inner_smul_left, inner_add_left, weighted_pairing T hT g hg ρ, weighted_pairing T hT g hg (reflectedZero ρ), mult_reflect]
    simp [a,b,reflectedZero_val,smul_eq_mul,div_eq_mul_inv,mul_comm,map_ofNat]
  have hn : ⟪negativeGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ, sourceEmbed T (problemOneL g)⟫_ℂ = (a-b)/2 := by
    unfold negativeGreenColumn
    rw [inner_smul_left, inner_sub_left, weighted_pairing T hT g hg ρ, weighted_pairing T hT g hg (reflectedZero ρ), mult_reflect]
    simp [a,b,reflectedZero_val,smul_eq_mul,div_eq_mul_inv,mul_comm,map_ofNat]
  rw [hp,hn,he]
  have hs : ((Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ)) ^ 2 = (zeroMult ρ.1 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : a * star b = (zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 * star (mellinHat g (mirror ρ.1))) := by
    dsimp [a,b]
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal]
    calc
      _ = ((Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ))^2 * (mellinHat g ρ.1 * (starRingEnd ℂ) (mellinHat g (mirror ρ.1))) := by ring
      _ = _ := by rw [hs]
  rw [hc]
theorem solution (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ) (hg : SupportedTest T g) :
    ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
      ‖(canonicalNegativeSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
        (weilDistribution (conv g (starInv g))).re := by
  let x := sourceEmbed T (problemOneL g)
  let v := fun τ => sourceEmbed T (actualGreenSource τ)
  have hs (w : CriticalZeros → Physical T) (hw : Summable (fun ρ => ‖w ρ‖ ^ 2)) : Summable (fun ρ => ‖⟪w ρ,x⟫_ℂ‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ρ => ?_) (hw.mul_right (‖x‖ ^ 2))
    exact (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (w ρ) x) 2)
  have hp := hs (positiveGreenColumn v) (canonical_actor_columns_summable T hT).1
  have hn := hs (negativeGreenColumn v) (canonical_actor_columns_summable T hT).2
  rw [canonicalPositiveSynthesis,canonicalNegativeSynthesis,columnSynthesis_adjoint_norm_sq,columnSynthesis_adjoint_norm_sq,← hp.tsum_sub hn]
  dsimp only [x,v]
  simp_rw [signed_pairing T hT g hg]
  have hq := ConnesRZ.explicit_formula (conv g (starInv g)) (isTest_conv hg.1 (isTest_starInv hg.1))
  simp_rw [ConnesRZ.mellinHat_conv_starInv g hg.1] at hq
  exact (Complex.hasSum_re hq).tsum_eq
