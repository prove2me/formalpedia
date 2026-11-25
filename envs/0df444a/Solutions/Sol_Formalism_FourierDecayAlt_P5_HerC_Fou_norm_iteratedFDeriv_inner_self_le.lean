-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.norm_iteratedFDeriv_inner_self_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:51:53.6329+00:00
-- url     : https://prove2.me/submissions/2cb931c5-db9b-437e-a8f4-308599ec592f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralIteratedFDerivEqZero
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_norm_iteratedFDeriv_id_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
  have hB := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear
    (f := (id : V → V)) (g := (id : V → V)) (N := ⊤) contDiff_id contDiff_id x (n := n) le_top
  have e : (fun y : V => (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (id y) (id y)) = fun y : V => inner ℝ y y := by
    funext y
    simp
  rw [e] at hB
  have hnB : ‖(innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)‖ ≤ 1 := norm_innerSL_le ℝ
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) * (1 + ‖x‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := norm_iteratedFDeriv_id_le i x
          have h2 := norm_iteratedFDeriv_id_le (n - i) x
          have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          gcongr
      _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]
          ring
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ := Finset.sum_nonneg fun i _ => by positivity
  calc ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ _ := hB
    _ ≤ 1 * (2 ^ n * (1 + ‖x‖) ^ 2) := mul_le_mul hnB hsum hS0 zero_le_one
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := one_mul _
end Formalism.FourierDecayAlt.P5.HerC.Fou
