-- Prove2me | solution 1 for ConnesGreen.canonical_scaled_covariance_le_iff_shell_conditions
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T05:09:09.409027+00:00
-- url     : https://prove2.me/submissions/42932b0c-a377-47fb-bb31-35c81344fa14

import Theorems.Thm_ConnesGreen_testVectorFamily_dense
import Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Theorems.Thm_WeilDefect_MarkerStability_nonnegative_iff_shell_and_cross_budget
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
private lemma shell_scaled_covariance_quadratic {H E F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (P : E →L[ℂ] H) (M : F →L[ℂ] H)
    (κ : ℝ) (x : H) :
    RCLike.re ⟪(κ • (P ∘L P.adjoint) - M ∘L M.adjoint) x, x⟫_ℂ =
      κ * ‖P.adjoint x‖ ^ 2 - ‖M.adjoint x‖ ^ 2 := by
  have hp := P.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  have hm := M.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] at hp hm
  simp only [sub_apply, smul_apply, inner_sub_left, inner_smul_left_eq_smul, RCLike.smul_re, map_sub, ContinuousLinearMap.comp_apply]
  rw [← hp, ← hm]

private lemma shell_scaled_selfAdjoint {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : E →L[ℂ] H) (κ : ℝ) (hκ : 0 ≤ κ) :
    IsSelfAdjoint (κ • (P ∘L P.adjoint)) := by
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (smul_nonneg hκ ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint P)))).isSelfAdjoint
private lemma shell_supported_mono {c T : ℝ} {g : ℝ → ℂ}
    (hg : SupportedTest c g) (hcT : c ≤ T) : SupportedTest T g := by
  refine ⟨hg.1, ?_⟩
  intro x hx
  obtain ⟨hl, hr⟩ := hg.2 hx
  constructor <;> linarith
private lemma shell_core_nonnegative
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (hcT : c ≤ T)
    (S : Finset CriticalZeros) (U : Physical c →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
      U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker c hc S)
    (κ : ℝ) (hκ : 1 ≤ κ) (x : Physical c) :
    0 ≤ RCLike.re ⟪(κ • canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint)
      (U x), U x⟫_ℂ := by
  let D := κ • canonicalPositiveCovariance T hT -
    canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
  have hclosed : IsClosed {x : Physical c | 0 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ} := by
    apply isClosed_le continuous_const
    exact Complex.continuous_re.comp ((D.continuous.comp U.continuous).inner U.continuous)
  have hrange : Set.range (fun g : {g : ℝ → ℂ // SupportedTest c g} =>
      sourceEmbed c (problemOneL g.1)) ⊆ {x : Physical c | 0 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ} := by
    rintro _ ⟨g, rfl⟩
    have hgT := shell_supported_mono g.2 hcT
    have hnonneg := (canonical_picard_half_iff_original_selected_tests c hc S).mp hhalf g.1 g.2
    obtain ⟨hpT, hmT⟩ := canonical_actor_test_norms_window_independent c T hc hT S g.1 g.2 hgT
    change 0 ≤ RCLike.re ⟪D (U (sourceEmbed c (problemOneL g.1))), U (sourceEmbed c (problemOneL g.1))⟫_ℂ
    rw [hU g.1 g.2]
    dsimp only [D, canonicalPositiveCovariance]
    rw [shell_scaled_covariance_quadratic (canonicalPositiveSynthesis T hT)
      (canonicalSelectedSynthesis T hT S) κ (sourceEmbed T (problemOneL g.1)), hpT, hmT]
    have hb := mul_nonneg (sub_nonneg.mpr hκ)
      (sq_nonneg ‖(canonicalPositiveSynthesis c hc).adjoint (sourceEmbed c (problemOneL g.1))‖)
    nlinarith
  have hsub := closure_minimal hrange hclosed
  rw [(testVectorFamily_dense c hc).closure_range] at hsub
  exact hsub (Set.mem_univ x)
theorem solution
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (hcT : c ≤ T)
    (S : Finset CriticalZeros) (U : Physical c →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
      U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker c hc S)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    let D := κ • canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
    (canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint ≤
      κ • canonicalPositiveCovariance T hT) ↔
    (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
      0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
    (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
      ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ) := by
  dsimp only
  rw [← sub_nonneg]
  have hd := (shell_scaled_selfAdjoint (canonicalPositiveSynthesis T hT) κ (by linarith : 0 ≤ κ)).sub
    (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalSelectedSynthesis T hT S)).isSelfAdjoint
  exact nonnegative_iff_shell_and_cross_budget _ hd U
    (shell_core_nonnegative c T hc hT hcT S U hU hhalf κ hκ)
