-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.deriv_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:10.986942+00:00
-- url     : https://prove2.me/submissions/3eff7dbc-a2d8-45d8-80bc-55e8e2496cd5

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_truncC
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_norm_coef_le
import Theorems.Thm_Formalism_LogFactorialMertensBounds_Icc_one_eq_Ioc
import Theorems.Thm_Formalism_LogFactorialMertensBounds_mertens_upper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0)
    (y z : ℝ) (hy : 1 ≤ y) (_hz : 1 ≤ z) :
    ‖GPsi D ell ψ y - GPsi D ell ψ z‖ ≤ |y - z| * (Real.log (max y z) + (Real.log 4 + 4) + ‖ell ψ‖) := by
  have hyM : ⌊y⌋₊ ≤ ⌊max y z⌋₊ := Nat.floor_le_floor (le_max_left _ _)
  have hzM : ⌊z⌋₊ ≤ ⌊max y z⌋₊ := Nat.floor_le_floor (le_max_right _ _)
  have hmax1 : 1 ≤ max y z := le_trans hy (le_max_left _ _)
  have hM1 : 1 ≤ ⌊max y z⌋₊ := Nat.le_floor (by simpa using hmax1)
  have ty := truncC (fun n => (Λ n : ℂ) * primVal D ψ n) y _ hyM
  have tz := truncC (fun n => (Λ n : ℂ) * primVal D ψ n) z _ hzM
  unfold GPsi
  rw [if_neg hψ, if_neg hψ, ty, tz]
  have e : (∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 : ℝ) : ℂ) + (y : ℂ) * ell ψ)
      - (∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n * ((max (z / n - 1) 0 : ℝ) : ℂ) + (z : ℂ) * ell ψ)
      = ∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)
        + ((y - z : ℝ) : ℂ) * ell ψ := by
    have : ∀ n : ℕ, (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)
        = (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 : ℝ) : ℂ)
          - (Λ n : ℂ) * primVal D ψ n * ((max (z / n - 1) 0 : ℝ) : ℂ) := by
      intro n; push_cast; ring
    simp only [this, Finset.sum_sub_distrib]
    push_cast; ring
  rw [e]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n
      * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)‖ ≤ |y - z| * Formalism.LogFactorialMertensBounds.A ⌊max y z⌋₊ := by
    refine le_trans (norm_sum_le _ _) ?_
    unfold Formalism.LogFactorialMertensBounds.A
    rw [← Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ha : |max (y / n - 1) 0 - max (z / n - 1) 0| ≤ |y - z| / n := by
      refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
      have : y / n - 1 - (z / n - 1) = (y - z) / n := by ring
      rw [this, abs_div, abs_of_pos hn0]
    calc ‖(Λ n : ℂ) * primVal D ψ n‖ * |max (y / n - 1) 0 - max (z / n - 1) 0|
        ≤ Λ n * (|y - z| / n) := mul_le_mul (norm_coef_le D ψ n) ha (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
      _ = |y - z| * (Λ n / n) := by ring
  have h2 : ‖((y - z : ℝ) : ℂ) * ell ψ‖ = |y - z| * ‖ell ψ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h3 := Formalism.LogFactorialMertensBounds.mertens_upper _ hM1
  have h4 : Real.log (⌊max y z⌋₊ : ℝ) ≤ Real.log (max y z) :=
    Real.log_le_log (by exact_mod_cast hM1) (Nat.floor_le (by linarith))
  rw [h2]
  have h5 : |y - z| * Formalism.LogFactorialMertensBounds.A ⌊max y z⌋₊ ≤ |y - z| * (Real.log (max y z) + (Real.log 4 + 4)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  nlinarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
