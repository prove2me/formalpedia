-- Prove2me | solution 1 for BianchiIX.hasDerivAt_projective_flow
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:27:41.580734+00:00
-- url     : https://prove2.me/submissions/fb03a628-55d2-481c-8faf-12eef116189a

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Theorems.Thm_BianchiIX_active_velocity_in_original_time
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveCoord
import Theorems.Thm_BianchiIX_phase_velocity_in_original_time
import Theorems.Thm_BianchiIX_strong_velocity_in_original_time
import Theorems.Thm_BianchiIX_weak_velocity_in_original_time
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open BianchiIX
noncomputable section


theorem solution
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt p (shearPlus (p t) (a t) (b t) (c t)) t)
    (hs : HasDerivAt s (shearMinus (s t) (a t) (b t) (c t)) t)
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t)
    (hA : 1 + p t ≠ 0) (hG : constraint (p t) (s t) (a t) (b t) (c t) = 1) :
    let m := projectiveCoord (p t) (s t)
    let u := projectiveCoord (p t) (a t)
    let v := projectiveCoord (p t) (b t)
    let w := projectiveCoord (p t) (c t)
    HasDerivAt (fun x => projectiveCoord (p x) (s x)) ((1 + p t) * phaseVelocity m u v w) t ∧
    HasDerivAt (fun x => projectiveCoord (p x) (a x)) ((1 + p t) * strongVelocity m u v w) t ∧
    HasDerivAt (fun x => projectiveCoord (p x) (b x)) ((1 + p t) * activeVelocity m u v w) t ∧
    HasDerivAt (fun x => projectiveCoord (p x) (c x)) ((1 + p t) * weakVelocity m u v w) t := by
  have hm := hasDerivAt_projectiveCoord hp hs hA
  have hu := hasDerivAt_projectiveCoord hp ha hA
  have hv := hasDerivAt_projectiveCoord hp hb hA
  have hw := hasDerivAt_projectiveCoord hp hc hA
  rw [phase_velocity_in_original_time hA] at hm
  rw [strong_velocity_in_original_time hA hG] at hu
  rw [active_velocity_in_original_time hA hG] at hv
  rw [weak_velocity_in_original_time hA hG] at hw
  exact ⟨hm, hu, hv, hw⟩
