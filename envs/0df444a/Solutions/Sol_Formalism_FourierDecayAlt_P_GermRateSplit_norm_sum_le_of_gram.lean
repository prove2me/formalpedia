-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermRateSplit.norm_sum_le_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:32:17.042274+00:00
-- url     : https://prove2.me/submissions/dfcaaa6c-7412-4ccb-ae15-368b6152d266

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfGram
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermRateSplit_norm_sq_comb
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermRateSplit_sum_sq_le_sq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRateSplit
open Finset
open scoped ComplexConjugate InnerProductSpace
namespace Formalism.FourierDecayAlt.P.GermRateSplit
theorem _root_.solution {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ P Q, k P Q = ⟪v P, v Q⟫_ℂ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = ∑ i, (c i : ℂ) * ⟪Y i (P l), Y i (P j)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ := by
  have h1 : ((‖∑ j ∈ J, a j • v (P j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_comb]
    calc ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * ⟪v (P j), v (P l)⟫_ℂ
        = ∑ j ∈ J, ∑ l ∈ J, ∑ i, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
          rw [← hv, hk j hj l hl, mul_sum]
          refine sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ j ∈ J, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          exact (sum_congr rfl fun j _ => sum_comm).trans sum_comm
      _ = ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
          refine sum_congr rfl fun i _ => ?_
          rw [Complex.ofReal_mul, norm_sq_comb, mul_sum, sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [Complex.conj_conj]
          ring
  have h2 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 := by
    exact_mod_cast h1
  have h3 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 ≤ (∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
    rw [h2]
    have : ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 =
        ∑ i, (√(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (hc i)]
    rw [this]
    exact sum_sq_le_sq_sum _ fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ :=
    sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (∑ j ∈ J, a j • v (P j))]
end Formalism.FourierDecayAlt.P.GermRateSplit
