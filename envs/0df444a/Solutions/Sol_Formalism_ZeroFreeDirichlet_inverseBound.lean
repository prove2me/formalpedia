-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.inverseBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:09.24311+00:00
-- url     : https://prove2.me/submissions/95ca88cb-cca3-401f-8357-0d34eabdf33b

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_term_twist_moebius_le
import Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_norm_term_one_succ
import Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_summable_shift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
open Formalism.ZF.MoebiusInverseZetaBounds
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : LInvBound := by
  intro q _ χ s hs
  have hσ1 : 0 < s.re - 1 := by linarith
  have hshift : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) ≤ s.re / (s.re - 1) := by
    apply Real.tsum_le_of_sum_range_le
    · intro n
      positivity
    · intro m
      rcases m with _ | k
      · simp only [Finset.range_zero, Finset.sum_empty]
        positivity
      · rw [Finset.sum_range_succ']
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hanti : AntitoneOn (fun x : ℝ => x ^ (-s.re)) (Set.Icc (1 : ℝ) (1 + k)) := by
          intro x hx y _ hxy
          exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
        have hsum := hanti.sum_le_integral
        have hint : ∫ x in (1 : ℝ)..(1 + k), x ^ (-s.re) =
            ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) := by
          apply integral_rpow
          refine Or.inr ⟨by linarith, ?_⟩
          rw [Set.uIcc_of_le (by linarith)]
          intro h
          linarith [h.1]
        have hpos : 0 ≤ (1 + k : ℝ) ^ (-s.re + 1) := by positivity
        have hb : ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) ≤ 1 / (s.re - 1) := by
          rw [Real.one_rpow, show -s.re + 1 = -(s.re - 1) by ring, div_neg, ← neg_div]
          have hpos' : 0 ≤ (1 + k : ℝ) ^ (-(s.re - 1)) := by positivity
          gcongr
          linarith
        have e : ∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) =
            ∑ i ∈ Finset.range k, (fun x : ℝ => x ^ (-s.re)) (1 + ((i + 1 : ℕ) : ℝ)) :=
          Finset.sum_congr rfl fun i _ => by
            show (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) = (1 + ((i + 1 : ℕ) : ℝ)) ^ (-s.re)
            congr 1 <;> ring
        rw [e]
        have e2 : s.re / (s.re - 1) = 1 / (s.re - 1) + 1 := by
          field_simp
          ring
        simp only [Nat.cast_zero, zero_add, Real.one_rpow]
        rw [hint] at hsum
        linarith
  have hp : -(s.re - 1) - 1 < -1 := by linarith
  have hfun : (fun n : ℕ => ‖term (1 : ℕ → ℂ) s (n + 1)‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) :=
    funext (norm_term_one_succ s)
  have hS1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1, hfun]
    exact summable_shift hp
  have hT1 : ∑' n, ‖term (1 : ℕ → ℂ) s n‖ ≤ s.re / (s.re - 1) := by
    rw [hS1.tsum_eq_zero_add, LSeries.term_zero, norm_zero, zero_add, hfun]
    exact hshift
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hinv : ‖LSeries ↗χ s‖⁻¹ = ‖LSeries (↗χ * ↗μ) s‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hmul]
  rw [hinv]
  have hS2 : Summable fun n => ‖term (↗χ * ↗μ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_term_twist_moebius_le χ s n) hS1
  calc ‖LSeries (↗χ * ↗μ) s‖ = ‖∑' n, term (↗χ * ↗μ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗μ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ :=
      Summable.tsum_le_tsum (fun n => norm_term_twist_moebius_le χ s n) hS2 hS1
    _ ≤ s.re / (s.re - 1) := hT1
end Formalism.ZeroFreeDirichlet
