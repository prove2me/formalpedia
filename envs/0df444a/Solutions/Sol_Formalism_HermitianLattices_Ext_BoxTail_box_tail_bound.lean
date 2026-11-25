-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.box_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:15.626585+00:00
-- url     : https://prove2.me/submissions/5c0b02ab-f659-401d-a887-d9aa2b68caf0

import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContour
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailDiff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailMertens
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailNum
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailFinal
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_contour
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_diff_schi
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_num


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxTailHyp ε C x₀ := by
  intro ε hε hε1
  obtain ⟨K, hK0, hK⟩ := tail_contour (ε / 1600) (by positivity) (by linarith)
  obtain ⟨CM, hCM0, hCM⟩ := tail_mertens
  obtain ⟨x₀, hx₀3, hnum⟩ := tail_num ε K hε hε1 hK0
  refine ⟨400 * CM + 1, x₀, ?_⟩
  intro x Q N _ χ hx hQlo hQhi hχ hgood
  obtain ⟨_, _, hNQ, hbox⟩ := hgood
  have hx3 : 3 ≤ x := le_trans hx₀3 hx
  have hx0 : 0 < x := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  have hlogQ1 : 1 ≤ Real.log Q := le_trans (Real.one_le_rpow (by linarith) (by positivity)) hQlo
  have hQ2 : 2 ≤ Q := by
    have : Real.exp 1 ≤ Q := by
      rw [← Real.exp_log hQ0]; exact Real.exp_le_exp.mpr hlogQ1
    linarith [Real.exp_one_gt_d9]
  have hnum' := hnum x Q hx hQ0 hQlo hQhi
  set z : ℝ := x ^ 400 with hz
  set η : ℝ := 1 / x ^ 2 with hη
  have hz1 : 1 ≤ z := one_le_pow₀ (by linarith)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  have hzη : 0 < z * η := by positivity
  have hC := hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1
  have hD := tail_diff_schi χ z (z * η) hz1 hzη
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have htail : Formalism.HermitianLattices.ZeroFreeRegionGL2.tailL χ z = Formalism.ZeroFreeDirichlet.negLD χ 1 - P := by
    simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.tailL, Formalism.HermitianLattices.ZeroFreeRegionGL2.logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, hP]
  have hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) =
      -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) +
      (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * P) := by ring
  have hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤
      (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + ε / 1600) + z ^ 2 / Q)
        + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η) := by
    rw [le_div_iff₀ hzη]
    have h1 := congrArg norm hkey
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le] at h1
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ * (z * η) = z * η * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        exact add_le_add hC hD
  have hfirst : ‖(x : ℂ) * Formalism.HermitianLattices.ZeroFreeRegionGL2.tailL χ z‖ ≤ x ^ ε := by
    rw [htail, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    refine le_trans ?_ hnum'
    exact mul_le_mul_of_nonneg_left hnorm hx0.le
  refine ⟨hfirst, ?_⟩

  have hz2 : 2 ≤ z := by
    have : (3 : ℝ) ≤ z := by
      rw [hz]; calc (3 : ℝ) ≤ x := hx3
        _ ≤ x ^ 400 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hPle : ‖P‖ ≤ CM * Real.log z := by
    refine le_trans (norm_sum_le _ _) (le_trans ?_ (hCM z hz2))
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (Λ n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (Λ n : ℝ) * 1 := by gcongr
      _ = Λ n := mul_one _
  have hlogz : Real.log z = 400 * Real.log x := by
    rw [hz, Real.log_pow]; norm_num
  have htail1 : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤ 1 := by
    have h2 : x * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤ x ^ ε := by
      have := hfirst
      rw [htail, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at this
      exact this
    have h3 : x ^ ε ≤ x := by
      calc x ^ ε ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hε1
        _ = x := Real.rpow_one x
    have h4 : x * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤ x * 1 := by linarith
    exact le_of_mul_le_mul_left h4 hx0
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hLD : Formalism.HermitianLattices.ZeroFreeRegionGL2.logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]
  rw [hLD, norm_neg]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1‖ = ‖P + (Formalism.ZeroFreeDirichlet.negLD χ 1 - P)‖ := by ring_nf
    _ ≤ ‖P‖ + ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := norm_add_le _ _
    _ ≤ CM * (400 * Real.log x) + 1 := by rw [← hlogz]; linarith
    _ ≤ (400 * CM + 1) * Real.log x := by nlinarith
end Formalism.HermitianLattices.Ext.BoxTail
