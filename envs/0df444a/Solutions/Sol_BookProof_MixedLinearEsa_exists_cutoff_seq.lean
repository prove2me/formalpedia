-- Prove2me | solution 1 for BookProof.MixedLinearEsa.exists_cutoff_seq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:50:15.944115+00:00
-- url     : https://prove2.me/submissions/a5ff59f2-8f71-4388-bb22-142677893500

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.exists_cutoff_seq
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
theorem h44_cutoff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ (cut : ℕ → V → ℝ) (K : ℝ),
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n)) ∧
      (∀ n, HasCompactSupport (cut n)) ∧
      (∀ n x, ‖cut n x‖ ≤ 1) ∧
      (∀ x : V, ∀ᶠ n in Filter.atTop, cut n x = 1 ∧ fderiv ℝ (cut n) x = 0) ∧
      (∀ n x, ‖fderiv ℝ (cut n) x‖ ≤ K) := by
  let χ : ContDiffBump (0 : V) := ⟨1, 2, by norm_num, by norm_num⟩
  have hχc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : V → ℝ) := χ.contDiff
  have hχd : Continuous (fderiv ℝ (χ : V → ℝ)) := hχc.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := hχd.bounded_above_of_compact_support (χ.hasCompactSupport.fderiv (𝕜 := ℝ))
  let c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hc0 : ∀ n, 0 < c n := fun n => by positivity
  have hc1 : ∀ n, c n ≤ 1 := fun n => inv_le_one_of_one_le₀ (by simp)
  have hder : ∀ n x, HasFDerivAt (fun y : V => χ (c n • y))
      ((fderiv ℝ (χ : V → ℝ) (c n • x)).comp (c n • ContinuousLinearMap.id ℝ V)) x := by
    intro n x
    have h1 : HasFDerivAt (fun y : V => c n • y) (c n • ContinuousLinearMap.id ℝ V) x :=
      (hasFDerivAt_id x).const_smul (c n)
    exact ((hχc.differentiable (by simp)) _).hasFDerivAt.comp x h1
  refine ⟨fun n y => χ (c n • y), K, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hχc.comp (contDiff_const_smul (c n))
  · intro n
    exact χ.hasCompactSupport.comp_smul (hc0 n).ne'
  · intro n x
    rw [Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact χ.le_one
  · intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hmem : c n • x ∈ Metric.ball (0 : V) χ.rIn := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (hc0 n)]
      show ((n : ℝ) + 1)⁻¹ * ‖x‖ < 1
      rw [inv_mul_lt_iff₀ (by positivity)]
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hev : (fun y : V => χ (c n • y)) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      have hcont : Continuous (fun y : V => c n • y) := continuous_const_smul _
      have := hcont.continuousAt.eventually (χ.eventuallyEq_one_of_mem_ball hmem)
      filter_upwards [this] with y hy
      simpa using hy
    refine ⟨?_, ?_⟩
    · exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hmem)
    · rw [hev.fderiv_eq]; simp
  · intro n x
    rw [(hder n x).fderiv]
    calc ‖(fderiv ℝ (χ : V → ℝ) (c n • x)).comp (c n • ContinuousLinearMap.id ℝ V)‖
        ≤ ‖fderiv ℝ (χ : V → ℝ) (c n • x)‖ * ‖c n • ContinuousLinearMap.id ℝ V‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * 1 := by
          apply mul_le_mul (hK _) _ (norm_nonneg _) ((norm_nonneg _).trans (hK 0))
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hc0 n)]
          calc c n * ‖ContinuousLinearMap.id ℝ V‖ ≤ 1 * 1 :=
                mul_le_mul (hc1 n) ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
            _ = 1 := by ring
      _ = K := by ring

theorem solution :
    ∃ (cut : ℕ → V → ℝ) (K : ℝ),
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n)) ∧
      (∀ n, HasCompactSupport (cut n)) ∧
      (∀ n x, ‖cut n x‖ ≤ 1) ∧
      (∀ x : V, ∀ᶠ n in Filter.atTop, cut n x = 1 ∧ fderiv ℝ (cut n) x = 0) ∧
      (∀ n x, ‖fderiv ℝ (cut n) x‖ ≤ K) := by
  exact h44_cutoff

