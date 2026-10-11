-- Prove2me | solution 1 for ConnesGreen.canonical_energy_scaled_finite_negative_weil_certificates
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T19:41:12.827332+00:00
-- url     : https://prove2.me/submissions/747e65e5-e083-4e74-83cd-f68dcb0cffcd

import Theorems.Thm_ConnesGreen_canonical_uniform_finite_negative_weil_certificates
import Theorems.Thm_ConnesRZ_explicit_formula
import Theorems.Thm_ConnesGreen_canonical_source_pairing_mellin
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
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
lemma ConnesGreen.real_complement_series {ι : Type*} [DecidableEq ι] (a : ι → ℝ)
    (ha : Summable a) (F : Finset ι) :
    Summable (fun i => if i ∈ F then 0 else a i) ∧
      (∑' i, if i ∈ F then 0 else a i) = ∑' i : {i : ι // i ∉ F}, a i.1 := by
  have hid : (fun i => if i ∈ F then 0 else a i) =
      ({i : ι | i ∉ F}).indicator a := by
    funext i
    by_cases hi : i ∈ F <;> simp [Set.indicator, hi]
  rw [hid]
  exact ⟨ha.indicator _, (tsum_subtype {i : ι | i ∉ F} a).symm⟩

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
lemma ConnesGreen.pairing_sq_energy_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u x : H) :
    ‖⟪u, x⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℂ) u x) 2

lemma ConnesGreen.adjoint_covariance_energy_bound {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : K →L[ℂ] H) (x : H) :
    ‖A.adjoint x‖ ^ 2 ≤ ‖A ∘L A.adjoint‖ * ‖x‖ ^ 2 := by
  have hcov : ‖A ∘L A.adjoint‖ = ‖A.adjoint‖ ^ 2 := by
    simpa only [ContinuousLinearMap.adjoint_adjoint, pow_two] using
      ContinuousLinearMap.norm_adjoint_comp_self A.adjoint
  calc
    _ ≤ ‖A.adjoint‖ ^ 2 * ‖x‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.adjoint.le_opNorm x) 2
    _ = ‖A ∘L A.adjoint‖ * ‖x‖ ^ 2 := by rw [hcov]

lemma ConnesGreen.actual_complement_bound_by_pair_covariances_energy
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros)
    (Ptail : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t)
    (hcolumns : ∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
      positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    :
    Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
    (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤
      (‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖) *
        ‖sourceEmbed t (problemOneL g)‖ ^ 2 := by
  let v := fun τ => sourceEmbed t (actualGreenSource τ)
  let x := sourceEmbed t (problemOneL g)
  let p := fun τ => ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2
  let n := fun τ => ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2
  have hp : Summable p := Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun τ => pairing_sq_energy_bound _ x) ((canonical_actor_columns_summable t ht).1.mul_right (‖x‖ ^ 2))
  have hn : Summable n := Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun τ => pairing_sq_energy_bound _ x) ((canonical_actor_columns_summable t ht).2.mul_right (‖x‖ ^ 2))
  let pc := fun τ => if τ ∈ F then 0 else p τ
  let nc := fun τ => if τ ∈ F then 0 else n τ
  have hpc := (real_complement_series p hp F).1
  have hnc := (real_complement_series n hn F).1
  have hbound : ∀ τ : CriticalZeros,
      ‖if τ ∈ F then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ ≤
      pc τ + nc τ := by
    intro τ
    by_cases hτ : τ ∈ F
    · simp [pc, nc, hτ]
    · simpa only [pc, nc, p, n, v, x, if_neg hτ] using
        actual_zero_term_norm_le_actor_energy t ht g hg τ
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hpc.add hnc)
  have hsumBound := hs.tsum_le_tsum hbound (hpc.add hnc)
  rw [hpc.tsum_add hnc] at hsumBound
  have hPeq := columnSynthesis_unique
    (fun τ : {τ : CriticalZeros // τ ∉ F} => positiveGreenColumn v τ.1)
    ((canonical_actor_columns_summable t ht).1.comp_injective Subtype.val_injective)
    Ptail hcolumns
  have hpId : ‖(ContinuousLinearMap.adjoint Ptail) x‖ ^ 2 = (∑' τ : CriticalZeros, pc τ) := by
    rw [hPeq, (real_complement_series p hp F).2]
    exact columnSynthesis_adjoint_norm_sq _ _ x
  have hnId : ‖(ContinuousLinearMap.adjoint (canonicalBackgroundSynthesis t ht F)) x‖ ^ 2 =
      (∑' τ : CriticalZeros, nc τ) := by
    rw [(real_complement_series n hn F).2]
    exact columnSynthesis_adjoint_norm_sq
      (fun τ : {τ : CriticalZeros // τ ∉ F} => negativeGreenColumn v τ.1)
      ((canonical_actor_columns_summable t ht).2.comp_injective Subtype.val_injective) x
  have hpBound := adjoint_covariance_energy_bound Ptail x
  have hnBound := adjoint_covariance_energy_bound (canonicalBackgroundSynthesis t ht F) x
  change _ ≤ ‖canonicalTailCovariance t ht F‖ * ‖x‖ ^ 2 at hnBound
  rw [hpId] at hpBound
  rw [hnId] at hnBound
  refine ⟨hs, ?_⟩
  rw [add_mul]
  linarith only [hsumBound, hpBound, hnBound]

lemma ConnesGreen.actual_finite_complex_error_bound
    (g : ℝ → ℂ) (hg : IsTest g) (F : Finset CriticalZeros)
    (hsum : Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖)) :
    ‖weilDistribution (conv g (starInv g)) -
      ∑ τ ∈ F, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ ≤
      ∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
        (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ := by
  have hc := actual_complement_hasSum g hg F
  have hn := norm_tsum_le_tsum_norm hsum
  rwa [hc.tsum_eq] at hn

lemma ConnesGreen.negative_iff_finite_margin_of_energy_error
    (q : ℝ) (a ε : ℕ → ℝ) (E : ℝ) (hε : Tendsto ε atTop (nhds 0))
    (herr : ∀ n, |q - a n| ≤ ε n * E) :
    (q < 0 ↔ ∃ n : ℕ, a n < -(ε n * E)) ∧
    (q < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n < -(ε n * E)) := by
  have hlim : Tendsto (fun n => ε n * E) atTop (nhds 0) := by
    simpa using hε.mul_const E
  have hforward : q < 0 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n < -(ε n * E) := by
    intro hq
    have hev : ∀ᶠ n in atTop, ε n * E < -q / 2 :=
      (tendsto_order.mp hlim).2 (-q / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, ?_⟩
    intro n hn
    have he := (abs_le.mp (herr n)).1
    have hh := hN n hn
    linarith
  have hreverse : (∃ n : ℕ, a n < -(ε n * E)) → q < 0 := by
    rintro ⟨n, hn⟩
    have he := (abs_le.mp (herr n)).2
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

lemma ConnesGreen.complex_limit_of_energy_error
    (q : ℂ) (a : ℕ → ℂ) (ε : ℕ → ℝ) (E : ℝ)
    (hε : Tendsto ε atTop (nhds 0)) (herr : ∀ n, ‖q - a n‖ ≤ ε n * E) :
    Tendsto a atTop (nhds q) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hlim : Tendsto (fun n => ε n * E) atTop (nhds 0) := by
    simpa using hε.mul_const E
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 δ hδ)
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [dist_eq_norm, norm_sub_rev] using (herr n).trans_lt (hN n hn)
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
           ((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -ε n))) ∧
      (∀ n : ℕ, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g →
          Summable (fun τ : CriticalZeros => ‖if τ ∈ F n then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
          (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤ ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2 ∧
          ‖(weilDistribution (conv g (starInv g))) - (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)‖ ≤ ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∀ g : ℝ → ℂ, SupportedTest t g →
          (((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ n : ℕ, (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -(ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2)) ∧
           ((weilDistribution (conv g (starInv g))).re < 0 ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re < -(ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2)) ∧
           Tendsto (fun n => (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)) atTop (nhds ((weilDistribution (conv g (starInv g))))))) := by
  obtain ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered, hequiv, hcommon, hunit, hcert⟩ :=
    canonical_uniform_finite_negative_weil_certificates T hT S K μ ε hμ hε hε1 hμlim hεlim
  have henergy : ∀ n : ℕ, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
      ∀ g : ℝ → ℂ, SupportedTest t g →
        Summable (fun τ : CriticalZeros => ‖if τ ∈ F n then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
        (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤ ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2 ∧
        ‖(weilDistribution (conv g (starInv g))) - (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)‖ ≤ ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2 := by
    intro n t ht htT g hg
    obtain ⟨Ptail, hcols, hsmall, hband, hactual⟩ := hstage n t ht htT
    obtain ⟨hsum, hbound⟩ := actual_complement_bound_by_pair_covariances_energy t ht (F n) Ptail hcols g hg
    have hb := hbound.trans (mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg ‖sourceEmbed t (problemOneL g)‖))
    exact ⟨hsum, hb, (actual_finite_complex_error_bound g hg.1 (F n) hsum).trans hb⟩
  refine ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered, hequiv, hcommon, hunit, hcert, henergy, ?_⟩
  intro t ht htT g hg
  have hreal : ∀ n, |(weilDistribution (conv g (starInv g))).re - (∑ τ ∈ F n, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| ≤ ε n * ‖sourceEmbed t (problemOneL g)‖ ^ 2 := by
    intro n
    exact (actual_finite_real_error_bound g hg.1 (F n) (henergy n t ht htT g hg).1).trans
      (henergy n t ht htT g hg).2.1
  have hsign := negative_iff_finite_margin_of_energy_error _ _ ε
    (‖sourceEmbed t (problemOneL g)‖ ^ 2) hεlim hreal
  refine ⟨hsign.1, hsign.2, ?_⟩
  exact complex_limit_of_energy_error _ _ ε (‖sourceEmbed t (problemOneL g)‖ ^ 2) hεlim
    (fun n => (henergy n t ht htT g hg).2.2)
