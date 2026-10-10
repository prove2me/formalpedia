-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_endpoint_failure_iff_physical_margin_or_all_margin_escape
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T08:15:13.474018+00:00
-- url     : https://prove2.me/submissions/8d24f2f6-87f0-4267-a339-1553a3977732

import Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_normalized_full_background_tests
import Theorems.Thm_ConnesGreen_canonical_uniform_bounded_selected_tests_iff_physical_margin
import Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
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

private lemma escape_supported_mono {t T : ℝ} {g : ℝ → ℂ}
    (hg : SupportedTest t g) (htT : t ≤ T) : SupportedTest T g := by
  refine ⟨hg.1, ?_⟩
  intro x hx
  have hs := hg.2 hx
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

private lemma escape_restored_independent (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (S : Finset CriticalZeros) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (hgT : SupportedTest T g) :
    (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 =
    (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 := by
  have h1 := normalized_positive_energy t ht S g hg
  have h2 := normalized_positive_energy T hT S g hgT
  obtain ⟨hp, ha⟩ := canonical_actor_test_norms_window_independent t T ht hT S g hg hgT
  rw [hp, ha] at h2
  linarith

private lemma escape_extend_family (c : ℝ) (hc : 0 < c)
    (S : Finset CriticalZeros) (δ : ℝ)
    (hb : ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
      ∃ g : ℝ → ℂ, SupportedTest T g ∧
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
        (weilDistribution (conv g (starInv g))).re +
          ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ) :
    ∀ T : ℝ, ∀ hT : 0 < T, c < T →
      ∃ g : ℝ → ℂ, SupportedTest T g ∧
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
        (weilDistribution (conv g (starInv g))).re +
          ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ := by
  intro T hT hcT
  by_cases hTc : T < c + 1
  · exact hb T hT hcT hTc
  · have ht : 0 < c + 1 / 2 := by linarith
    obtain ⟨g, hg, ha, hw⟩ := hb (c + 1 / 2) ht (by linarith) (by linarith)
    have hgT := escape_supported_mono hg (by linarith : c + 1 / 2 ≤ T)
    refine ⟨g, hgT, ?_, ?_⟩
    · exact (canonical_actor_test_norms_window_independent
        (c + 1 / 2) T ht hT S g hg hgT).2.trans ha
    · rwa [← escape_restored_independent (c + 1 / 2) T ht hT S g hg hgT]

private lemma escape_no_physical_margin (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (hno : ¬ (∃ ε : ℝ, 0 < ε ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ M : ℝ, 0 < M → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
        ∀ g : ℝ → ℂ, SupportedTest T g →
          ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 →
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ →
          M < ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
            (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)) := by
  classical
  intro M hM
  have hnotbounded := mt (canonical_uniform_bounded_selected_tests_iff_physical_margin c hc S).mp hno
  have hnotall : ¬ (∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
      ∃ g : ℝ → ℂ, SupportedTest T g ∧
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
        ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
          (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)) ≤ M ∧
        (weilDistribution (conv g (starInv g))).re +
          ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ) := by
    intro hb
    exact hnotbounded ⟨δ, hδ, hδ1, M, hM, hb⟩
  obtain ⟨t, hbad⟩ := not_forall.mp hnotall
  obtain ⟨ht, hbad⟩ := not_forall.mp hbad
  obtain ⟨hct, hbad⟩ := _root_.not_imp.mp hbad
  obtain ⟨ht1, hnone⟩ := _root_.not_imp.mp hbad
  let r := min ((t - c) / 2) (1 / 2)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨r, hr, hr1, ?_⟩
  intro T hT hcT hTr g hg ha hw
  have hTt : T < t := by
    have hrl : r ≤ (t - c) / 2 := min_le_left _ _
    linarith
  have hgt := escape_supported_mono hg hTt.le
  have hat : ‖(canonicalSelectedSynthesis t ht S).adjoint
      (sourceEmbed t (problemOneL g))‖ ^ 2 = 1 :=
    (canonical_actor_test_norms_window_independent T t hT ht S g hg hgt).2.trans ha
  have hwt : (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < -δ := by
    rwa [← escape_restored_independent T t hT ht S g hg hgt]
  by_contra hn
  exact hnone ⟨g, hgt, hat, le_of_not_gt hn, hwt⟩
theorem ConnesGreen.canonical_no_physical_margin_iff_all_margin_dirichlet_escape (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros) :
    (¬ (∃ ε : ℝ, 0 < ε ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT S).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε) ↔ (∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ M : ℝ, 0 < M → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
          ∀ g : ℝ → ℂ, SupportedTest T g →
            ‖(canonicalSelectedSynthesis T hT S).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 →
            (weilDistribution (conv g (starInv g))).re +
              ‖(canonicalBackgroundSynthesis T hT S).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ →
            M < ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
              (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)))) := by
  classical
  constructor
  · intro hno δ hδ hδ1
    exact escape_no_physical_margin c hc S hno δ hδ hδ1
  · intro hescape hgap
    obtain ⟨δ, hδ, hδ1, M, hM, hb⟩ :=
      (canonical_uniform_bounded_selected_tests_iff_physical_margin c hc S).mpr hgap
    obtain ⟨r, hr, hr1, he⟩ := hescape δ hδ hδ1 M hM
    have ht : 0 < c + r / 2 := by linarith
    obtain ⟨g, hg, ha, hE, hw⟩ := hb (c + r / 2) ht (by linarith) (by linarith)
    have hlarge := he (c + r / 2) ht (by linarith) (by linarith) g hg ha hw
    exact (not_lt_of_ge hE) hlarge
theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
(¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        (∃ ε : ℝ, 0 < ε ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε) ∨
        ((∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
            (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ) ∧ (∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ M : ℝ, 0 < M → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
          ∀ g : ℝ → ℂ, SupportedTest T g →
            ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 →
            (weilDistribution (conv g (starInv g))).re +
              ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ →
            M < ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
              (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ :=
    canonical_quartet_endpoint_failure_iff_normalized_full_background_tests ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  constructor
  · intro hfailure
    by_cases hgap : ∃ ε : ℝ, 0 < ε ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
          ∃ g : ℝ → ℂ, SupportedTest T g ∧
            ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
            (weilDistribution (conv g (starInv g))).re +
              ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε
    · exact Or.inl hgap
    · obtain ⟨δ, hδ, hδ1, hb⟩ := he.mp hfailure
      refine Or.inr ⟨⟨δ, hδ, hδ1, ?_⟩,
        (canonical_no_physical_margin_iff_all_margin_dirichlet_escape c hc (quartet ρ)).mp hgap⟩
      intro T hT hcT
      obtain ⟨g, hg, ha, hw, _⟩ := hb T hT hcT
      exact ⟨g, hg, ha, hw⟩
  · intro hbranches
    have hfamily : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∀ T : ℝ, ∀ hT : 0 < T, c < T →
          ∃ g : ℝ → ℂ, SupportedTest T g ∧
            ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
            (weilDistribution (conv g (starInv g))).re +
              ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ := by
      rcases hbranches with hgap | ⟨⟨δ, hδ, hδ1, hb⟩, _⟩
      · obtain ⟨δ, hδ, hδ1, M, hM, hb⟩ :=
          (canonical_uniform_bounded_selected_tests_iff_physical_margin c hc (quartet ρ)).mpr hgap
        refine ⟨δ, hδ, hδ1, escape_extend_family c hc (quartet ρ) δ ?_⟩
        intro T hT hcT hTc
        obtain ⟨g, hg, ha, _, hw⟩ := hb T hT hcT hTc
        exact ⟨g, hg, ha, hw⟩
      · exact ⟨δ, hδ, hδ1, hb⟩
    obtain ⟨δ, hδ, hδ1, hb⟩ := hfamily
    apply he.mpr
    refine ⟨δ, hδ, hδ1, ?_⟩
    intro T hT hcT
    obtain ⟨g, hg, ha, hw⟩ := hb T hT hcT
    refine ⟨g, hg, ha, hw, ?_⟩
    have hn := sq_nonneg ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
      (sourceEmbed T (problemOneL g))‖
    linarith
