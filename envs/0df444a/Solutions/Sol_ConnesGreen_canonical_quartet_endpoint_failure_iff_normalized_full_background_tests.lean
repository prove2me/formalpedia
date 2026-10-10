-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_endpoint_failure_iff_normalized_full_background_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T07:14:13.040471+00:00
-- url     : https://prove2.me/submissions/7113fe77-d750-40d2-827a-7d12dc9086ec

import Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_uniform_full_background_tests
import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
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

private lemma normalized_witness (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (κ : ℝ) (hκ : 1 < κ)
    (hw : κ * ((weilDistribution (conv g (starInv g))).re +
      ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2) <
      -(κ - 1) * ‖(canonicalSelectedSynthesis t ht S).adjoint
        (sourceEmbed t (problemOneL g))‖ ^ 2) :
    ∃ h : ℝ → ℂ, SupportedTest t h ∧
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL h))‖ ^ 2 = 1 ∧
      (weilDistribution (conv h (starInv h))).re +
        ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL h))‖ ^ 2 <
        -(1 - κ⁻¹) := by
  let a := ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖
  have ha : 0 < a := by
    have hp := normalized_positive_energy t ht S g hg
    have hpos := sq_nonneg ‖(canonicalPositiveSynthesis t ht).adjoint
      (sourceEmbed t (problemOneL g))‖
    have han := norm_nonneg ((canonicalSelectedSynthesis t ht S).adjoint
      (sourceEmbed t (problemOneL g)))
    change 0 < a
    by_contra hn
    have hz : a = 0 := le_antisymm (le_of_not_gt hn) han
    change κ * _ < -(κ - 1) * a ^ 2 at hw
    change _ + a ^ 2 + _ = _ at hp
    rw [hz] at hw hp
    nlinarith
  let r := a⁻¹
  have hr : r ^ 2 * a ^ 2 = 1 := by
    dsimp [r]
    field_simp
  have hrpos : 0 < r ^ 2 := sq_pos_of_pos (inv_pos.mpr ha)
  let h := (r : ℂ) • g
  have hnorm : ‖(canonicalSelectedSynthesis t ht S).adjoint
      (sourceEmbed t (problemOneL h))‖ ^ 2 = 1 := by
    simp only [h]
    rw [normalized_source_smul t ht g hg (r : ℂ), normalized_actor_energy_smul]
    exact hr
  refine ⟨h, normalized_supported_smul hg _, hnorm, ?_⟩
  have hscaled := mul_lt_mul_of_pos_left hw hrpos
  have hinv : κ * κ⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  simp only [h]
  rw [normalized_weil_smul t ht S g hg r, normalized_source_smul t ht g hg,
    normalized_actor_energy_smul]
  change r ^ 2 * (κ * _) < r ^ 2 * (-(κ - 1) * a ^ 2) at hscaled
  have hs : κ * (r ^ 2 * (weilDistribution (conv g (starInv g))).re +
      r ^ 2 * ‖(canonicalBackgroundSynthesis t ht S).adjoint
        (sourceEmbed t (problemOneL g))‖ ^ 2) < -(κ - 1) := by
    nlinarith [hr]
  nlinarith

private lemma normalized_endpoint_coefficient (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1 / 2) : 1 < ((1 / 2 - η)⁻¹ - 1) := by
  have hi := one_div_lt_one_div_of_lt (by linarith : 0 < (1 / 2 : ℝ) - η)
    (by linarith : (1 / 2 : ℝ) - η < 1 / 2)
  norm_num at hi
  linarith

private lemma normalized_reserve_coefficient (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      (((1 / 2 - η)⁻¹ - 1) - 1) < ((1 / 2 - η)⁻¹ - 1) * δ := by
  let η := δ / 8
  have hη : 0 < η := by dsimp [η]; positivity
  have hηhalf : η < 1 / 2 := by dsimp [η]; linarith
  refine ⟨η, hη, hηhalf, ?_⟩
  have hp : 0 < (1 / 2 : ℝ) - η := by linarith
  apply (mul_lt_mul_iff_right₀ hp).mp
  have hi : ((1 / 2 : ℝ) - η)⁻¹ * (1 / 2 - η) = 1 := inv_mul_cancel₀ hp.ne'
  dsimp [η] at *
  nlinarith
theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      (¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          ∀ T : ℝ, ∀ hT : 0 < T, c < T →
            ∃ g : ℝ → ℂ, SupportedTest T g ∧
              ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
              (weilDistribution (conv g (starInv g))).re +
                ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ ∧
              (weilDistribution (conv g (starInv g))).re < -δ) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ :=
    canonical_quartet_endpoint_failure_iff_uniform_full_background_tests ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  constructor
  · intro hno
    obtain ⟨η, hη, hηhalf, hb⟩ := he.mp hno
    let κ := ((1 / 2 - η)⁻¹ - 1)
    have hκ : 1 < κ := normalized_endpoint_coefficient η hη hηhalf
    have hik : 0 < κ⁻¹ := inv_pos.mpr (by linarith)
    have hi1 : κ⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < κ)).mpr hκ
    refine ⟨1 - κ⁻¹, by linarith, by linarith, ?_⟩
    intro T hT hcT
    obtain ⟨g, hg, hw, _⟩ := hb T hT hcT
    obtain ⟨h, hh, hn, hr⟩ := normalized_witness T hT (quartet ρ) g hg κ hκ hw
    refine ⟨h, hh, hn, hr, ?_⟩
    have hbn := sq_nonneg ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
      (sourceEmbed T (problemOneL h))‖
    linarith
  · rintro ⟨δ, hδ, hδ1, hb⟩
    obtain ⟨η, hη, hηhalf, hreserve⟩ := normalized_reserve_coefficient δ hδ hδ1
    apply he.mpr
    refine ⟨η, hη, hηhalf, ?_⟩
    intro T hT hcT
    obtain ⟨g, hg, hn, hw, hneg⟩ := hb T hT hcT
    refine ⟨g, hg, ?_, ?_, by linarith⟩
    · rw [hn]
      have hκ := normalized_endpoint_coefficient η hη hηhalf
      nlinarith
    · linarith
