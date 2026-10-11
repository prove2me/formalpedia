-- Prove2me | solution 1 for ConnesGreen.canonical_uniform_band_actual_tail_marker_recovery
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T17:45:16.380474+00:00
-- url     : https://prove2.me/submissions/8ee99b28-160f-48d4-b245-dba7b005b4b4

import Theorems.Thm_ConnesGreen_RG0Integration_uniform_original_pair_actor_tail
import Theorems.Thm_WeilDefect_MarkerStability_tail_marker_stability
import Theorems.Thm_WeilDefect_MarkerStability_covariance_relative_bound_all_regularizations_iff_zero
import Theorems.Thm_ConnesGreen_canonical_source_pairing_mellin
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
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

lemma ConnesGreen.nonnegative_finite_tail {ι : Type*} [DecidableEq ι] (a : ι → ℝ)
    (ha : Summable a) (ha0 : ∀ i, 0 ≤ a i) (S : Finset ι)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ι, S ⊆ F ∧ (∑' i, if i ∈ F then 0 else a i) < ε := by
  have he : ∀ᶠ F : Finset ι in Filter.atTop, (∑' i, a i) - ε < ∑ i ∈ F, a i :=
    (tendsto_order.mp ha.hasSum).1 _ (by linarith)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp he
  let F := F₀ ∪ S
  refine ⟨F, Finset.subset_union_right, ?_⟩
  have hnear := hF₀ F Finset.subset_union_left
  have hid := ha.sum_add_tsum_subtype_compl F
  rw [← (real_complement_series a ha F).2] at hid
  linarith only [hnear, hid]

lemma ConnesGreen.unit_pairing_sq_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u x : H) (hx : ‖x‖ ^ 2 ≤ 1) :
    ‖⟪u, x⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  calc
    _ ≤ ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ) u x) 2
    _ ≤ ‖u‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
    _ = _ := mul_one _

lemma ConnesGreen.adjoint_covariance_unit_bound {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : K →L[ℂ] H) (x : H) (hx : ‖x‖ ^ 2 ≤ 1) :
    ‖A.adjoint x‖ ^ 2 ≤ ‖A ∘L A.adjoint‖ := by
  have hcov : ‖A ∘L A.adjoint‖ = ‖A.adjoint‖ ^ 2 := by
    simpa only [ContinuousLinearMap.adjoint_adjoint, pow_two] using
      ContinuousLinearMap.norm_adjoint_comp_self A.adjoint
  calc
    _ ≤ ‖A.adjoint‖ ^ 2 * ‖x‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.adjoint.le_opNorm x) 2
    _ = ‖A ∘L A.adjoint‖ * ‖x‖ ^ 2 := by rw [hcov]
    _ ≤ ‖A ∘L A.adjoint‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = _ := mul_one _

lemma ConnesGreen.actual_complement_bound_by_pair_covariances
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros)
    (Ptail : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t)
    (hcolumns : ∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
      positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hx : ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1) :
    Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
    (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
      (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ≤
      ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ := by
  let v := fun τ => sourceEmbed t (actualGreenSource τ)
  let x := sourceEmbed t (problemOneL g)
  let p := fun τ => ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2
  let n := fun τ => ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2
  have hp : Summable p := Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun τ => unit_pairing_sq_bound _ x hx) (canonical_actor_columns_summable t ht).1
  have hn : Summable n := Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun τ => unit_pairing_sq_bound _ x hx) (canonical_actor_columns_summable t ht).2
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
  have hpBound := adjoint_covariance_unit_bound Ptail x hx
  have hnBound := adjoint_covariance_unit_bound (canonicalBackgroundSynthesis t ht F) x hx
  change _ ≤ ‖canonicalTailCovariance t ht F‖ at hnBound
  rw [hpId] at hpBound
  rw [hnId] at hnBound
  refine ⟨hs, ?_⟩
  linarith only [hsumBound, hpBound, hnBound]

lemma ConnesGreen.canonical_fixed_cutoff_all_scales_iff_negative_columns_zero
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) (α : ℝ) (hα : 0 ≤ α) :
    (∀ μ : ℝ, 0 < μ → ‖canonicalTailCovariance t ht F‖ ≤ α * μ) ↔
      ∀ τ : CriticalZeros, τ ∉ F →
        negativeGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ = 0 := by
  have hz := covariance_relative_bound_all_regularizations_iff_zero
    (canonicalBackgroundSynthesis t ht F) α hα
  change (∀ μ : ℝ, 0 < μ → ‖canonicalTailCovariance t ht F‖ ≤ α * μ) ↔
    canonicalBackgroundSynthesis t ht F = 0 at hz
  rw [hz]
  constructor
  · intro h τ hτ
    let i : {τ : CriticalZeros // τ ∉ F} := ⟨τ, hτ⟩
    have hh := congrArg (fun B : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t =>
      B (lp.single 2 i (1 : ℂ))) h
    rw [canonicalBackgroundSynthesis_single] at hh
    simpa only [ContinuousLinearMap.zero_apply, i] using hh
  · intro h
    have hh := columnSynthesis_unique
      (fun τ : {τ : CriticalZeros // τ ∉ F} =>
        negativeGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1)
      ((canonical_actor_columns_summable t ht).2.comp_injective Subtype.val_injective)
      (0 : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t)
      (fun τ => by simp only [ContinuousLinearMap.zero_apply, h τ.1 τ.2])
    exact hh.symm

theorem solution
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (η μ₀ α : ℝ) (hη : 0 < η) (hμ₀ : 0 < μ₀) (hα : 0 < α) (hα1 : α < 1) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∀ τ ∈ F, reflectedZero τ ∈ F) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ < η ∧
          (∀ μ : ℝ, μ₀ ≤ μ →
            ‖canonicalTailCovariance t ht F‖ ≤ α * μ ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + μ • 1 - canonicalTailCovariance t ht F) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + μ • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + μ • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + μ • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + μ • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S)‖ ≤ α) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < η) ∧
          ((∀ μ : ℝ, 0 < μ → ‖canonicalTailCovariance t ht F‖ ≤ α * μ) ↔
            ∀ τ : CriticalZeros, τ ∉ F →
              negativeGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ = 0) := by
  let d : ℝ := min η (α * μ₀)
  have hd : 0 < d := lt_min hη (mul_pos hα hμ₀)
  obtain ⟨F, hSF, hclosed, htail⟩ :=
    ConnesGreen.RG0Integration.uniform_original_pair_actor_tail T hT S d hd
  refine ⟨F, hSF, hclosed, ?_⟩
  intro t ht htT
  obtain ⟨Ptail, hcolumns, hsmall⟩ := htail t ht htT
  have hηsmall : ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ < η :=
    hsmall.trans_le (min_le_left _ _)
  have hR : ‖canonicalTailCovariance t ht F‖ ≤ α * μ₀ := by
    have hpn : 0 ≤ ‖Ptail ∘L Ptail.adjoint‖ := norm_nonneg _
    have hdle : d ≤ α * μ₀ := min_le_right _ _
    linarith only [hsmall, hpn, hdle]
  refine ⟨Ptail, hcolumns, hηsmall, ?_, ?_,
    canonical_fixed_cutoff_all_scales_iff_negative_columns_zero t ht F α hα.le⟩
  · intro μ hμ
    have hμpos : 0 < μ := hμ₀.trans_le hμ
    have hb : ‖canonicalTailCovariance t ht F‖ ≤ α * μ :=
      hR.trans (mul_le_mul_of_nonneg_left hμ hα.le)
    have hL : 0 ≤ canonicalPositiveCovariance t ht :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalPositiveSynthesis t ht))
    have hB : 0 ≤ canonicalTailCovariance t ht F :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalBackgroundSynthesis t ht F))
    exact ⟨hb, tail_marker_stability _ _ (canonicalSelectedSynthesis t ht S)
      hL hB μ α hμpos hα.le hα1 hb⟩
  · intro g hg hx
    obtain ⟨hs, hb⟩ := actual_complement_bound_by_pair_covariances t ht F Ptail hcolumns g hg hx
    exact ⟨hs, hb.trans_lt hηsmall⟩
