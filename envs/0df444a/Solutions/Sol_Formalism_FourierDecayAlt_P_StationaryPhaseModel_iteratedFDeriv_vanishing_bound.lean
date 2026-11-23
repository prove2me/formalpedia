-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.iteratedFDeriv_vanishing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:19.479802+00:00
-- url     : https://prove2.me/submissions/9a1df3bc-3867-4826-a4d8-533e3cd28629

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {f : E → F} {r M : ℝ} (p : ℕ) (hp : p ≤ N) (hf : ContDiff ℝ N f)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (h0 : ∀ i : ℕ, i < p → iteratedFDeriv ℝ i f 0 = 0) (k : ℕ) (hk : k ≤ p) :
    ∀ x ∈ Metric.closedBall (0 : E) r, ‖iteratedFDeriv ℝ (p - k) f x‖ ≤ M * ‖x‖ ^ k := by
  induction k with
  | zero =>
    intro x hx
    simpa using hM x hx p hp
  | succ k ih =>
    intro x hx
    have ih := ih (Nat.le_of_succ_le hk)
    have hxr : ‖x‖ ≤ r := by simpa using hx
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx 0 (Nat.zero_le _))
    have e : p - (k + 1) + 1 = p - k := by omega
    have hlt : p - (k + 1) < N := by omega
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ (p - (k + 1)) f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast hlt)
    have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
        ‖fderiv ℝ (iteratedFDeriv ℝ (p - (k + 1)) f) y‖ ≤ M * ‖x‖ ^ k := by
      intro y hy
      have hyx : ‖y‖ ≤ ‖x‖ := by simpa using hy
      rw [norm_fderiv_iteratedFDeriv, e]
      refine (ih y (by simpa using hyx.trans hxr)).trans ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hyx k) hM0
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun y _ => hdiff y) hb
      (convex_closedBall (0 : E) ‖x‖) (by simp : (0 : E) ∈ Metric.closedBall (0 : E) ‖x‖)
      (by simp : x ∈ Metric.closedBall (0 : E) ‖x‖)
    rw [h0 _ (by omega), sub_zero, sub_zero] at h
    rw [pow_succ, ← mul_assoc]
    exact h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
