-- Prove2me | solution 1 for Formalism.REAL.integral_right_derivative_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:11.931833+00:00
-- url     : https://prove2.me/submissions/1a2900e3-96e3-4ca2-87c8-0190ecca370f

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_frobenius_nonneg
import Theorems.Thm_Formalism_REAL_frobenius_mul_le
import Theorems.Thm_Formalism_REAL_mul_exp_zero_smul
import Theorems.Thm_Formalism_REAL_continuous_frobenius_exp_neg_smul
import Theorems.Thm_Formalism_REAL_hasDerivAt_right_translate
import Theorems.Thm_Formalism_REAL_right_derivative_zero_outside_support
import Theorems.Thm_Formalism_REAL_continuous_smooth_on_group
import Theorems.Thm_Formalism_REAL_isCompact_frobenius_sublevel
import Theorems.Thm_Formalism_REAL_exp_indefinite_unitary_holds
import Theorems.Thm_Formalism_REAL_indefinite_unitary_mul_mem
import Theorems.Thm_Formalism_REAL_indefinite_unitary_unimodular
import Theorems.Thm_Formalism_REAL_one_parameter_subgroup_holds
import Theorems.Thm_Formalism_REAL_rdSmooth_of
import Theorems.Thm_Formalism_REAL_right_derivative_extends


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution : IntRdZero := by
  intro n ε φ X R hφ hX hsupp
  let E : ℝ → UJ ε := fun t =>
    indefiniteUnitaryMk ε (NormedSpace.exp ((t : ℂ) • X)) (exp_indefinite_unitary_holds n ε X hX t)
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  have hcφ := continuous_smooth_on_group hφ
  have hcR := continuous_smooth_on_group (rdSmooth_of right_derivative_extends n ε φ X hφ hX)
  obtain ⟨M0, hM0⟩ := (isCompact_frobenius_sublevel ε R).exists_bound_of_continuousOn hcR.continuousOn
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_frobenius_exp_neg_smul X).continuousOn
  let M := max M0 0
  let K' := {g : UJ ε | hsG g ≤ R * M1}
  let F : ℝ → UJ ε → ℂ := fun t g => φ (toM g * NormedSpace.exp ((t : ℂ) • X))
  let F' : ℝ → UJ ε → ℂ := fun t g => Rd X φ (toM g * NormedSpace.exp ((t : ℂ) • X))
  let bound : UJ ε → ℝ := K'.indicator (fun _ => M)
  have hFc : ∀ t, Continuous (F t) := fun t => by
    have := hcφ.comp (continuous_mul_const (E t)); exact this
  have hF'c : ∀ t, Continuous (F' t) := fun t => by
    have := hcR.comp (continuous_mul_const (E t)); exact this
  have hint0 : Integrable (F 0) (muG ε) := by
    refine (hFc 0).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_frobenius_sublevel ε R) ?_)
    intro g hg
    simp only [Set.mem_ofPred_eq, not_le] at hg
    show φ (toM g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 0
    rw [mul_exp_zero_smul]
    exact hsupp _ g.2 hg
  have hbound : ∀ g : UJ ε, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t g‖ ≤ bound g := by
    intro g t ht
    have hh : inUJ ε (toM g * NormedSpace.exp ((t : ℂ) • X)) :=
      indefinite_unitary_mul_mem ε g.2 (exp_indefinite_unitary_holds n ε X hX t)
    by_cases hc : hs (toM g * NormedSpace.exp ((t : ℂ) • X)) ≤ R
    · have hM : ‖F' t g‖ ≤ M := (hM0 (g * E t) hc).trans (le_max_left _ _)
      have hmem : g ∈ K' := by
        have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
          exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
        have h1 := hM1 t ht'
        rw [Real.norm_eq_abs] at h1
        have h2 : hs (NormedSpace.exp (((-t : ℝ) : ℂ) • X)) ≤ M1 := (le_abs_self _).trans h1
        have hR0 : 0 ≤ R := (frobenius_nonneg _).trans hc
        have hg : toM g = (toM g * NormedSpace.exp ((t : ℂ) • X)) *
            NormedSpace.exp (((-t : ℝ) : ℂ) • X) := by
          rw [Matrix.mul_assoc, ← one_parameter_subgroup_holds n X t (-t), add_neg_cancel, mul_exp_zero_smul]
        show hs (toM g) ≤ R * M1
        rw [hg]
        exact (frobenius_mul_le _ _).trans (mul_le_mul hc h2 (frobenius_nonneg _) hR0)
      show ‖F' t g‖ ≤ K'.indicator (fun _ => M) g
      rw [Set.indicator_of_mem hmem]
      exact hM
    · push Not at hc
      have h0 : F' t g = 0 := right_derivative_zero_outside_support hX hh hsupp hc
      rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) g
  have hbint : Integrable bound (muG ε) := by
    refine (integrable_indicator_iff (isCompact_frobenius_sublevel ε (R * M1)).isClosed.measurableSet).2 ?_
    exact integrableOn_const (isCompact_frobenius_sublevel ε (R * M1)).measure_lt_top.ne
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muG ε) (F := F) (F' := F')
    (x₀ := 0) (bound := bound) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable) hint0
    (hF'c 0).aestronglyMeasurable (ae_of_all _ hbound) hbint
    (ae_of_all _ fun g t _ => hasDerivAt_right_translate hφ hX g.2 t)
  have hconst : (fun t => ∫ g, F t g ∂(muG ε)) = fun _ => ∫ g, φ (toM g) ∂(muG ε) := by
    funext t
    exact integral_mul_right_eq_self (fun g => φ (toM g)) (E t)
  rw [hconst] at key
  have h0 := key.2.unique (hasDerivAt_const (0 : ℝ) _)
  simpa only [F', mul_exp_zero_smul] using h0
end Formalism.REAL
