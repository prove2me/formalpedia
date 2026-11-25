-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.cutTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:28.475549+00:00
-- url     : https://prove2.me/submissions/fdcc44dd-d192-4012-8056-8f1fcfef1b6d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_cutBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_smoothLog_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_thetaBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_thetaSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : CutTheta := by
  intro hC c σ ε h4 hε p
  choose Cc hCc using fun i => cutBound c 1 i le_rfl
  have hexp : ∀ ε₂ x : ℝ, ld p (fun y => c.sc ε₂ 1 y * th ε σ y) x =
      ∑ i ∈ range (p + 1), (p.choose i : ℝ) * ld i (c.sc ε₂ 1) x * ld (p - i) (th ε σ) x := by
    intro ε₂ x
    unfold ld
    have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => c.sc ε₂ 1 (Real.exp u)) := smoothLog_sc c ε₂ 1
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => th ε σ (Real.exp u)) := thetaSmooth ε σ hε
    exact iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by exact_mod_cast le_top))
      (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  refine ⟨∑ i ∈ range (p + 1), (p.choose i : ℝ) * Cc i *
      (Real.exp 1 * (p - i).factorial * (4 * σ) ^ (p - i)), fun ε₂ x h2 hx => ⟨?_, ?_⟩⟩
  · rw [hexp, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have a := (hCc i ε₂ x h2 hx).1
    have b := thetaBound hC σ ε h4 hε (p - i) x hx
    calc (p.choose i : ℝ) * |ld i (c.sc ε₂ 1) x| * |ld (p - i) (th ε σ) x|
        ≤ ((p.choose i : ℝ) * Cc i) * (Real.exp 1 * (p - i).factorial * (4 * σ) ^ (p - i) * th ε σ x) :=
          mul_le_mul (mul_le_mul_of_nonneg_left a (Nat.cast_nonneg _)) b (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans a))
      _ = _ := by ring
  · intro hlt
    rw [hexp, Finset.sum_eq_single 0]
    · rw [(hCc 0 ε₂ x h2 hx).2.2 hlt]; simp
    · intro i _ hi
      rw [(hCc i ε₂ x h2 hx).2.2 hlt, if_neg hi]; simp
    · simp
end Formalism.FourierDecayAlt.P.LEx1
