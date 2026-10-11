-- Prove2me | solution 1 for ConnesGreen.canonical_uniform_actual_zero_tail_control
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T17:24:46.727881+00:00
-- url     : https://prove2.me/submissions/7b41246b-52e3-4dbc-89e7-9e466a85ff6c

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

theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (ε : ℝ) (hε : 0 < ε) :
    let v := fun τ : CriticalZeros => sourceEmbed t (actualGreenSource τ)
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∑' τ : CriticalZeros, if τ ∈ F then 0 else
        ‖positiveGreenColumn v τ‖ ^ 2 + ‖negativeGreenColumn v τ‖ ^ 2) < ε ∧
      ∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
        let x := sourceEmbed t (problemOneL g)
        Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
          (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
        (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
          (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε ∧
        (0 ≤ ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 ∧
          ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 < ε) ∧
        ‖(canonicalBackgroundSynthesis t ht S).adjoint x‖ ^ 2 =
          (∑ τ ∈ F \ S, ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2) +
            ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 ∧
        (0 ≤ ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
          (∑ τ ∈ F, ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2) ∧
          ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
            (∑ τ ∈ F, ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2) < ε) := by
  dsimp only
  let v := fun τ : CriticalZeros => sourceEmbed t (actualGreenSource τ)
  let cp := fun τ => ‖positiveGreenColumn v τ‖ ^ 2
  let cn := fun τ => ‖negativeGreenColumn v τ‖ ^ 2
  let C := fun τ => cp τ + cn τ
  have hcp : Summable cp := (canonical_actor_columns_summable t ht).1
  have hcn : Summable cn := (canonical_actor_columns_summable t ht).2
  have hC : Summable C := hcp.add hcn
  have hC0 : ∀ τ, 0 ≤ C τ := by intro τ; dsimp [C, cp, cn]; positivity
  obtain ⟨F, hSF, hsmall⟩ := nonnegative_finite_tail C hC hC0 S ε hε
  refine ⟨F, hSF, hsmall, ?_⟩
  intro g hg hx
  let x := sourceEmbed t (problemOneL g)
  let p := fun τ => ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2
  let n := fun τ => ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2
  have hpC : ∀ τ, p τ ≤ cp τ := fun τ => unit_pairing_sq_bound _ x hx
  have hnC : ∀ τ, n τ ≤ cn τ := fun τ => unit_pairing_sq_bound _ x hx
  have hp : Summable p := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpC hcp
  have hn : Summable n := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hnC hcn
  let pc := fun τ => if τ ∈ F then 0 else p τ
  let nc := fun τ => if τ ∈ F then 0 else n τ
  let cc := fun τ => if τ ∈ F then 0 else C τ
  have hpc := (real_complement_series p hp F).1
  have hnc := (real_complement_series n hn F).1
  have hcc := (real_complement_series C hC F).1
  have hpcC : ∀ τ, pc τ ≤ cc τ := by
    intro τ
    by_cases hτ : τ ∈ F
    · simp [pc, cc, hτ]
    · simp only [pc, cc, if_neg hτ]
      have hh := hpC τ
      have hh0 : 0 ≤ cn τ := sq_nonneg _
      dsimp [C]
      linarith only [hh, hh0]
  have hncC : ∀ τ, nc τ ≤ cc τ := by
    intro τ
    by_cases hτ : τ ∈ F
    · simp [nc, cc, hτ]
    · simp only [nc, cc, if_neg hτ]
      have hh := hnC τ
      have hh0 : 0 ≤ cp τ := sq_nonneg _
      dsimp [C]
      linarith only [hh, hh0]
  have hpTail : (∑' τ, pc τ) < ε := (hpc.tsum_le_tsum hpcC hcc).trans_lt hsmall
  have hnTail : (∑' τ, nc τ) < ε := (hnc.tsum_le_tsum hncC hcc).trans_lt hsmall
  have hqBound : ∀ τ : CriticalZeros,
      ‖if τ ∈ F then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖ ≤ cc τ := by
    intro τ
    by_cases hτ : τ ∈ F
    · simp [cc, hτ]
    · simp only [cc, if_neg hτ]
      have hq := actual_zero_term_norm_le_actor_energy t ht g hg τ
      have hpcτ := hpC τ
      have hncτ := hnC τ
      change _ ≤ p τ + n τ at hq
      change _ ≤ cp τ + cn τ
      linarith only [hq, hpcτ, hncτ]
  have hqs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hqBound hcc
  have hqTail := (hqs.tsum_le_tsum hqBound hcc).trans_lt hsmall
  have hbF : ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 = (∑' τ, nc τ) := by
    rw [(real_complement_series n hn F).2]
    exact columnSynthesis_adjoint_norm_sq
      (fun τ : {τ : CriticalZeros // τ ∉ F} => negativeGreenColumn v τ.1)
      (hcn.comp_injective Subtype.val_injective) x
  let nS := fun τ => if τ ∈ S then 0 else n τ
  have hnS := (real_complement_series n hn S).1
  have hbS : ‖(canonicalBackgroundSynthesis t ht S).adjoint x‖ ^ 2 = (∑' τ, nS τ) := by
    rw [(real_complement_series n hn S).2]
    exact columnSynthesis_adjoint_norm_sq
      (fun τ : {τ : CriticalZeros // τ ∉ S} => negativeGreenColumn v τ.1)
      (hcn.comp_injective Subtype.val_injective) x
  have hnest : (fun τ => if τ ∈ F then 0 else nS τ) = nc := by
    funext τ
    by_cases hτ : τ ∈ F
    · simp [nc, hτ]
    · have hτS : τ ∉ S := fun h => hτ (hSF h)
      simp [nc, nS, hτ, hτS]
  have hhead : (∑ τ ∈ F, nS τ) = ∑ τ ∈ F \ S, n τ := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro τ hτ
    by_cases hτS : τ ∈ S <;> simp [nS, hτS]
  have hpartition := hnS.sum_add_tsum_subtype_compl F
  rw [← (real_complement_series nS hnS F).2, hnest, hhead] at hpartition
  have hbg : ‖(canonicalBackgroundSynthesis t ht S).adjoint x‖ ^ 2 =
      (∑ τ ∈ F \ S, n τ) + ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 := by
    rw [hbS, hbF]
    exact hpartition.symm
  have hpId : ‖(ContinuousLinearMap.adjoint (canonicalPositiveSynthesis t ht)) x‖ ^ 2 = (∑' τ : CriticalZeros, p τ) := by
    exact columnSynthesis_adjoint_norm_sq (positiveGreenColumn v) hcp x
  have hpositivePartition := hp.sum_add_tsum_subtype_compl F
  rw [← (real_complement_series p hp F).2] at hpositivePartition
  have hpositiveRemainder : ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      (∑ τ ∈ F, p τ) = (∑' τ, pc τ) := by
    rw [hpId]
    linarith only [hpositivePartition]
  refine ⟨hqs, hqTail, ⟨sq_nonneg _, ?_⟩, hbg, ?_⟩
  · rwa [hbF]
  · rw [hpositiveRemainder]
    refine ⟨tsum_nonneg (fun τ => ?_), hpTail⟩
    dsimp [pc, p]
    split_ifs <;> positivity
