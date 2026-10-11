-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_escape_fixed_carrier_neutral_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T13:41:11.207814+00:00
-- url     : https://prove2.me/submissions/eb2e486e-a5a6-4d43-94e7-91edf7d7b9d5

import Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_physical_margin_or_all_margin_escape
import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
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
private theorem amr_partition_helper (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (h : Physical t) :
    ‖(ContinuousLinearMap.adjoint (canonicalSelectedSynthesis t ht S)) h‖ ^ 2 +
      ‖(ContinuousLinearMap.adjoint (canonicalBackgroundSynthesis t ht S)) h‖ ^ 2 =
      ‖(ContinuousLinearMap.adjoint (canonicalNegativeSynthesis t ht)) h‖ ^ 2 := by
  rw [canonicalSelectedSynthesis, canonicalBackgroundSynthesis, canonicalNegativeSynthesis,
    columnSynthesis_adjoint_norm_sq, columnSynthesis_adjoint_norm_sq,
    columnSynthesis_adjoint_norm_sq]
  have hs : Summable (fun ρ : CriticalZeros =>
      ‖⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, h⟫_ℂ‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ρ => ?_) ((canonical_actor_columns_summable t ht).2.mul_right (‖h‖ ^ 2))
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ)
          (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) h) 2
  exact hs.tsum_subtype_add_tsum_subtype_compl (S : Set CriticalZeros)

private lemma amr_canonical_positive_covariance_arithmetic_energy
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    RCLike.re ⟪canonicalPositiveCovariance t ht (sourceEmbed t (problemOneL g)),
      sourceEmbed t (problemOneL g)⟫_ℂ =
      (weilDistribution (conv g (starInv g))).re +
        ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
        ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  let x := sourceEmbed t (problemOneL g)
  have he := canonical_signed_actor_arithmetic t ht g hg
  have hpart := amr_partition_helper t ht S x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp
  change RCLike.re ⟪(canonicalPositiveSynthesis t ht ∘L (canonicalPositiveSynthesis t ht).adjoint) x, x⟫_ℂ = _
  rw [← hp]
  dsimp [x] at *
  linarith
private lemma normalized_supported_smul {t : ℝ} {g : ℝ → ℂ}
    (hg : SupportedTest t g) (a : ℂ) : SupportedTest t (a • g) := by
  refine ⟨⟨hg.1.1.const_smul a, hg.1.2.smul_left⟩, ?_⟩
  exact (tsupport_smul_subset_right (fun _ : ℝ => a) g).trans hg.2

private lemma normalized_continuous_memLp (t : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) : MemLp f 2 (windowMeasure t) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc

private lemma normalized_windowL2_smul (t : ℝ) (g : ℝ → ℂ)
    (hg : MemLp g 2 (windowMeasure t)) (a : ℂ) :
    windowL2 t (a • g) = a • windowL2 t g := by
  simp only [windowL2, dif_pos hg, dif_pos (hg.const_smul a)]
  exact MemLp.toLp_const_smul a hg

private lemma normalized_energy_smul (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (a : ℂ) :
    energyVector t (a • g) = a • energyVector t g := by
  have hd : iteratedDeriv 1 (a • g) = a • iteratedDeriv 1 g := by
    funext x
    exact iteratedDeriv_const_smul (hg.1.1.of_le (by simp)).contDiffAt a
  have eg := normalized_continuous_memLp t g hg.1.1.continuous
  have ed := normalized_continuous_memLp t (iteratedDeriv 1 g)
    (hg.1.1.continuous_iteratedDeriv 1 (by simp))
  apply (WithLp.equiv 2 _).injective
  funext i
  fin_cases i
  · change windowL2 t (iteratedDeriv 1 (a • g)) = _
    rw [hd, normalized_windowL2_smul t _ ed a]
    rfl
  · change (1 / 2 : ℂ) • windowL2 t (a • g) = a • ((1 / 2 : ℂ) • windowL2 t g)
    rw [normalized_windowL2_smul t _ eg a]
    exact smul_comm _ _ _

private lemma normalized_source_smul (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (a : ℂ) :
    sourceEmbed t (problemOneL (a • g)) = a • sourceEmbed t (problemOneL g) := by
  apply Subtype.ext
  simp only [RG0Integration.sourceEmbed_L_energyVector t ht _
    (normalized_supported_smul hg a), RG0Integration.sourceEmbed_L_energyVector t ht g hg,
    Submodule.coe_smul]
  exact normalized_energy_smul t g hg a

private lemma normalized_actor_energy_smul {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : H →L[ℂ] E) (x : H) (r : ℝ) :
    ‖A ((r : ℂ) • x)‖ ^ 2 = r ^ 2 * ‖A x‖ ^ 2 := by
  rw [map_smul, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma normalized_positive_energy (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
      ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 =
      ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  rw [← amr_canonical_positive_covariance_arithmetic_energy t ht S g hg]
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left
    (sourceEmbed t (problemOneL g))
  simpa only [canonicalPositiveCovariance, ContinuousLinearMap.adjoint_adjoint] using hp.symm

private lemma normalized_weil_smul (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (g : ℝ → ℂ) (hg : SupportedTest t g) (r : ℝ) :
    (weilDistribution (conv ((r : ℂ) • g) (starInv ((r : ℂ) • g)))).re =
      r ^ 2 * (weilDistribution (conv g (starInv g))).re := by
  have h1 := normalized_positive_energy t ht S g hg
  have h2 := normalized_positive_energy t ht S ((r : ℂ) • g)
    (normalized_supported_smul hg _)
  rw [normalized_source_smul t ht g hg] at h2
  simp only [normalized_actor_energy_smul] at h2
  nlinarith [h1]

private lemma bounded_inverse_normalization {a : ℝ} (ha : 0 < a) :
    (a⁻¹) ^ 2 * a ^ 2 = 1 := by
  field_simp

private lemma bounded_scaled_negative {n M w δ q : ℝ}
    (hq : 0 < q) (hqn : q * n = 1) (hnM : n ≤ M)
    (hM : 0 < M) (hδ : 0 < δ) (hw : w < -δ) :
    q * w < -(δ / (M + 1)) := by
  have hqM : 1 ≤ q * M := by nlinarith
  have hreserve : δ / (M + 1) ≤ q * δ := by
    apply (div_le_iff₀ (by linarith : 0 < M + 1)).mpr
    have hm := mul_le_mul_of_nonneg_right hqM hδ.le
    nlinarith
  have hs := mul_lt_mul_of_pos_left hw hq
  nlinarith

private lemma bounded_source_energy_scale (T : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) (r : ℝ) :
    ‖sourceEmbed T (problemOneL ((r : ℂ) • g))‖ ^ 2 =
      r ^ 2 * ‖sourceEmbed T (problemOneL g)‖ ^ 2 := by
  rw [normalized_source_smul T hT g hg (r : ℂ), norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma bounded_selected_scale (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest T g) (r : ℝ) :
    ‖(canonicalSelectedSynthesis T hT S).adjoint
      (sourceEmbed T (problemOneL ((r : ℂ) • g)))‖ ^ 2 =
      r ^ 2 * ‖(canonicalSelectedSynthesis T hT S).adjoint
        (sourceEmbed T (problemOneL g))‖ ^ 2 := by
  rw [normalized_source_smul T hT g hg (r : ℂ), normalized_actor_energy_smul]

private lemma bounded_restored_scale (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest T g) (r : ℝ) :
    (weilDistribution (conv ((r : ℂ) • g) (starInv ((r : ℂ) • g)))).re +
      ‖(canonicalBackgroundSynthesis T hT S).adjoint
        (sourceEmbed T (problemOneL ((r : ℂ) • g)))‖ ^ 2 =
      r ^ 2 * ((weilDistribution (conv g (starInv g))).re +
        ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2) := by
  rw [normalized_weil_smul T hT S g hg r,
    normalized_source_smul T hT g hg (r : ℂ), normalized_actor_energy_smul]
  ring
theorem ConnesGreen.canonical_escape_fixed_carrier_neutral_tests
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (δ : ℝ) (hδ : 0 < δ) (hf : ∀ T : ℝ, ∀ hT : 0 < T, c < T →
    ∃ g : ℝ → ℂ, SupportedTest T g ∧
      ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
      (weilDistribution (conv g (starInv g))).re +
        ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ) (he : ∀ M : ℝ, 0 < M → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
    ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
      ∀ g : ℝ → ℂ, SupportedTest T g →
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 →
        (weilDistribution (conv g (starInv g))).re +
          ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ →
        M < ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
          (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) S).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) S).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) S).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) S).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) S).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2) := by
  classical
  intro ε hε
  obtain ⟨r, hr, hr1, hescape⟩ := he ε⁻¹ (inv_pos.mpr hε)
  refine ⟨r, hr, hr1, ?_⟩
  intro T hT hcT hTr
  obtain ⟨g, hg, ha, hw⟩ := hf T hT hcT
  have hE := hescape T hT hcT hTr g hg ha hw
  rw [← actual_physical_test_norm T hT g hg] at hE
  let n := ‖sourceEmbed T (problemOneL g)‖
  change ε⁻¹ < n ^ 2 at hE
  have hn0 : 0 ≤ n := norm_nonneg _
  have hn2 : 0 < n ^ 2 := (inv_pos.mpr hε).trans hE
  have hn : 0 < n := by nlinarith only [hn0, hn2]
  let q : ℝ := (n⁻¹) ^ 2
  have hq : 0 < q := sq_pos_of_pos (inv_pos.mpr hn)
  have hqn : q * n ^ 2 = 1 := bounded_inverse_normalization hn
  have hmul : 1 < ε * n ^ 2 := by
    have hm := mul_lt_mul_of_pos_left hE hε
    simpa only [mul_inv_cancel₀ hε.ne'] using hm
  have hqε : q < ε := by nlinarith [sq_pos_of_pos hn]
  let h : ℝ → ℂ := ((n⁻¹ : ℝ) : ℂ) • g
  have hh : SupportedTest T h := normalized_supported_smul hg _
  have hc1 : 0 < c + 1 := by linarith
  have hT1 : T < c + 1 := by linarith
  have hh1 : SupportedTest (c + 1) h := by
    refine ⟨hh.1, ?_⟩
    intro x hx
    have hs := hh.2 hx
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hunitT : ‖sourceEmbed T (problemOneL h)‖ ^ 2 = 1 := by
    rw [show h = ((n⁻¹ : ℝ) : ℂ) • g from rfl,
      bounded_source_energy_scale T hT g hg n⁻¹]
    exact hqn
  have hunit : ‖sourceEmbed (c + 1) (problemOneL h)‖ ^ 2 = 1 := by
    rw [actual_physical_test_norm (c + 1) hc1 h hh1,
      ← actual_physical_test_norm T hT h hh]
    exact hunitT
  have haT : ‖(canonicalSelectedSynthesis T hT S).adjoint
      (sourceEmbed T (problemOneL h))‖ ^ 2 = q := by
    rw [show h = ((n⁻¹ : ℝ) : ℂ) • g from rfl,
      bounded_selected_scale T hT S g hg n⁻¹, ha, mul_one]
  have hscaled := bounded_restored_scale T hT S g hg n⁻¹
  have hneg : (weilDistribution (conv h (starInv h))).re +
      ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL h))‖ ^ 2 < -δ * q := by
    change _ = q * _ at hscaled
    change (weilDistribution (conv h (starInv h))).re +
      ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL h))‖ ^ 2 = _ at hscaled
    rw [hscaled]
    have hm := mul_lt_mul_of_pos_left hw hq
    nlinarith
  have henergy := normalized_positive_energy T hT S h hh
  have hout := normalized_positive_energy (c + 1) hc1 S h hh1
  obtain ⟨hp, hat⟩ := canonical_actor_test_norms_window_independent T (c + 1) hT hc1 S h hh hh1
  have hrestored : (weilDistribution (conv h (starInv h))).re +
      ‖(canonicalBackgroundSynthesis (c + 1) hc1 S).adjoint (sourceEmbed (c + 1) (problemOneL h))‖ ^ 2 =
      (weilDistribution (conv h (starInv h))).re +
        ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL h))‖ ^ 2 := by
    rw [hp, hat] at hout
    linarith
  have hap : ‖(canonicalSelectedSynthesis (c + 1) hc1 S).adjoint
      (sourceEmbed (c + 1) (problemOneL h))‖ ^ 2 = q := hat.trans haT
  have hpos := sq_nonneg ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL h))‖
  have hdq : 0 < δ * q := mul_pos hδ hq
  refine ⟨h, hh, hunit, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rwa [hap], by rwa [hap]⟩
  · refine ⟨sq_nonneg _, ?_⟩
    rw [hp]
    rw [haT] at henergy
    linarith
  · rw [hrestored]
    rw [haT] at henergy
    linarith
  · rwa [hrestored, hap]
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
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by
  classical
  obtain ⟨c, hc, hrc, hcut, hiff⟩ :=
    canonical_quartet_endpoint_failure_iff_physical_margin_or_all_margin_escape ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  intro hfailure hno
  rcases hiff.mp hfailure with hgap | ⟨⟨δ, hδ, hδ1, hf⟩, he⟩
  · exact (hno hgap).elim
  · exact ⟨δ, hδ, hδ1,
      canonical_escape_fixed_carrier_neutral_tests c hc (quartet ρ) δ hδ hf (he δ hδ hδ1)⟩
