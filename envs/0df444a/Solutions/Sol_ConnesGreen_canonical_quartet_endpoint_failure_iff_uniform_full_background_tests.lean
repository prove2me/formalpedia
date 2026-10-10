-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_endpoint_failure_iff_uniform_full_background_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T06:54:54.384919+00:00
-- url     : https://prove2.me/submissions/e0ebc592-85da-4149-a518-d4bc5406eba4

import Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_uniform_shell_witnesses
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
import Theorems.Thm_ConnesGreen_canonical_scaled_covariance_le_iff_shell_conditions
import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
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
private lemma shell_scaled_selfAdjoint {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : E →L[ℂ] H) (κ : ℝ) (hκ : 0 ≤ κ) :
    IsSelfAdjoint (κ • (P ∘L P.adjoint)) := by
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (smul_nonneg hκ ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint P)))).isSelfAdjoint
private lemma shell_witness_iff_full_background_test
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (hcT : c ≤ T)
    (S : Finset CriticalZeros) (U : Physical c →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
      U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker c hc S)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    (let D := κ • canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
     (∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
       RCLike.re ⟪D z, z⟫_ℂ < 0) ∨
     (∃ x : Physical c, ∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
       RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ < ‖⟪D (U x), z⟫_ℂ‖ ^ 2)) ↔
    ∃ g : ℝ → ℂ, SupportedTest T g ∧
      κ * ((weilDistribution (conv g (starInv g))).re +
        ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2) <
      -(κ - 1) * ‖(canonicalSelectedSynthesis T hT S).adjoint
        (sourceEmbed T (problemOneL g))‖ ^ 2 := by
  classical
  have he := not_congr (canonical_scaled_covariance_le_iff_shell_conditions
    c T hc hT hcT S U hU hhalf κ hκ)
  dsimp only at he ⊢
  push +distrib Not at he
  rw [← he]
  have hsa : IsSelfAdjoint (κ • canonicalPositiveCovariance T hT) :=
    shell_scaled_selfAdjoint (canonicalPositiveSynthesis T hT) κ (by linarith)
  rw [covariance_le_iff_original_tests T hT (κ • canonicalPositiveCovariance T hT)
    hsa (canonicalSelectedSynthesis T hT S)]
  push Not
  apply exists_congr
  intro g
  apply and_congr_right
  intro hg
  have hr : RCLike.re ⟪(κ • canonicalPositiveCovariance T hT)
      (sourceEmbed T (problemOneL g)), sourceEmbed T (problemOneL g)⟫_ℂ =
      κ * RCLike.re ⟪canonicalPositiveCovariance T hT
        (sourceEmbed T (problemOneL g)), sourceEmbed T (problemOneL g)⟫_ℂ := by
    letI := InnerProductSpace.rclikeToReal ℂ (Physical T)
    simp only [← real_inner_eq_re_inner ℂ, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  rw [hr, amr_canonical_positive_covariance_arithmetic_energy T hT S g hg]
  constructor <;> intro h <;> nlinarith
private lemma endpoint_coefficient_ge_one (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1 / 2) : 1 ≤ ((1 / 2 - η)⁻¹ - 1) := by
  have hi := one_div_lt_one_div_of_lt (by linarith : 0 < (1 / 2 : ℝ) - η)
    (by linarith : (1 / 2 : ℝ) - η < 1 / 2)
  norm_num at hi
  linarith
private lemma full_background_dominance {κ w a b : ℝ} (hκ : 1 ≤ κ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : κ * (w + b) < -(κ - 1) * a) :
    b < -w ∧ w < 0 := by
  have hκpos : 0 < κ := by linarith
  have hreserve := mul_nonneg (sub_nonneg.mpr hκ) ha
  have hn : w + b < 0 := by
    by_contra hno
    have hnonneg := mul_nonneg hκpos.le (le_of_not_gt hno)
    linarith
  constructor <;> linarith
theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      (¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
          ∀ T : ℝ, ∀ hT : 0 < T, c < T →
            ∃ g : ℝ → ℂ, SupportedTest T g ∧
              (((1 / 2 - η)⁻¹ - 1) *
                ((weilDistribution (conv g (starInv g))).re +
                  ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                    (sourceEmbed T (problemOneL g))‖ ^ 2) <
                -(((1 / 2 - η)⁻¹ - 1) - 1) *
                  ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                    (sourceEmbed T (problemOneL g))‖ ^ 2) ∧
              ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 <
                -(weilDistribution (conv g (starInv g))).re ∧
              (weilDistribution (conv g (starInv g))).re < 0) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ :=
    canonical_quartet_endpoint_failure_iff_uniform_shell_witnesses ρ hoff
  have hhalf := (hcut c hc).mpr le_rfl
  refine ⟨c, hc, hrc, hcut, ?_⟩
  constructor
  · intro hno
    obtain ⟨η, hη, hηhalf, hb⟩ := he.mp hno
    have hκ := endpoint_coefficient_ge_one η hη hηhalf
    refine ⟨η, hη, hηhalf, ?_⟩
    intro T hT hcT
    obtain ⟨U, hU⟩ := (hb T hT hcT).1
    obtain ⟨g, hg, hw⟩ := (shell_witness_iff_full_background_test c T hc hT hcT.le
      (quartet ρ) U hU hhalf _ hκ).mp ((hb T hT hcT).2 U hU)
    exact ⟨g, hg, hw, full_background_dominance hκ (sq_nonneg _) (sq_nonneg _) hw⟩
  · rintro ⟨η, hη, hηhalf, hb⟩
    apply he.mpr
    refine ⟨η, hη, hηhalf, ?_⟩
    intro T hT hcT
    refine ⟨exists_original_window_inclusion c T hc hT hcT.le, ?_⟩
    intro U hU
    obtain ⟨g, hg, hw, _⟩ := hb T hT hcT
    exact (shell_witness_iff_full_background_test c T hc hT hcT.le
      (quartet ρ) U hU hhalf _ (endpoint_coefficient_ge_one η hη hηhalf)).mpr ⟨g, hg, hw⟩
