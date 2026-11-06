-- Prove2me | solution 1 for BianchiIX.exists_scaled_connectionLog_reparametrization
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:52:34.490774+00:00
-- url     : https://prove2.me/submissions/35343788-1649-4e99-b236-91a5b41d02fc

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_convex_positiveIntegralClock_target
import Theorems.Thm_BianchiIX_hasDerivAt_positiveIntegralClock_symm
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_positiveIntegralClock_symm_zero
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiff_connectionClockRate (n : WithTop ℕ∞) : ContDiff ℝ n connectionClockRate := by
  unfold connectionClockRate connectionSpeed coupling
  fun_prop

private theorem BianchiIX.hasDerivAt_connectionLog_scaled {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hw : β t 3 ≠ 0) :
    HasDerivAt (fun s => Real.log (β s 3)) (a * connectionClockRate (β t)) t := by
  have H := (hasDerivAt_pi.mp hβ 3).log hw
  convert! H using 1
  change a * connectionClockRate (β t) = a * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3) / β t 3
  dsimp [connectionClockRate, connectionSpeed, weakVelocity]
  field_simp

/-- The growing wall is an exact clock on the whole chosen positive-rate interval. -/
theorem solution {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {s : ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (ha : ContinuousOn a I) (hapos : ∀ t ∈ I, 0 < a t)
    (hβ : ∀ t ∈ I, HasDerivAt β (a t • projectiveField (β t)) t)
    (hw : ∀ t ∈ I, 0 < β t 3) (hD : ∀ t ∈ I, 0 < connectionClockRate (β t)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = Real.log (β t 3) - Real.log (β s 3)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        HasDerivAt e.symm (1 / (a (e.symm z) * connectionClockRate (β (e.symm z)))) z ∧
        β (e.symm z) 3 = β s 3 * Real.exp z ∧
        HasDerivAt (fun u => β (e.symm u)) (connectionLogField (β (e.symm z))) z) := by
  let q : ℝ → ℝ := fun t => a t * connectionClockRate (β t)
  have hq : ContinuousOn q I := ha.mul ((contDiff_connectionClockRate 1).continuous.comp_continuousOn
    (HasDerivAt.continuousOn hβ))
  have hqpos : ∀ t ∈ I, 0 < q t := fun t ht => mul_pos (hapos t ht) (hD t ht)
  have hz (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun u => Real.log (β u 3)) (q t) t :=
    hasDerivAt_connectionLog_scaled (hβ t ht) (ne_of_gt (hw t ht))
  have hg (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun u => integralClock q s u + Real.log (β s 3)) (q t) t :=
    (hasStrictDerivAt_integralClock hI ho hq hs ht).hasDerivAt.add_const _
  have heq : I.EqOn (fun t => Real.log (β t 3))
      (fun t => integralClock q s t + Real.log (β s 3)) :=
    ho.eqOn_of_deriv_eq hI.isPreconnected
      (fun t ht => (hz t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hz t ht).deriv.trans (hg t ht).deriv.symm) hs (by rw [integralClock_initial, zero_add])
  let e := positiveIntegralClock hI ho hq hs hqpos
  have he0 : e s = 0 := integralClock_initial q s
  refine ⟨e, rfl, ?_, convex_positiveIntegralClock_target hI ho hq hs hqpos,
    he0 ▸ e.map_source hs, positiveIntegralClock_symm_zero hI ho hq hs hqpos,
    strictMonoOn_integralClock hI ho hq hs hqpos, ?_⟩
  · intro t ht
    change integralClock q s t = _
    linarith only [heq ht]
  · intro z hzmem
    have ht : e.symm z ∈ I := e.map_target hzmem
    have hinv := hasDerivAt_positiveIntegralClock_symm hI ho hq hs hqpos hzmem
    have htime : Real.log (β (e.symm z) 3) = z + Real.log (β s 3) := by
      have H := heq ht
      change _ = e (e.symm z) + _ at H
      rwa [e.right_inv hzmem] at H
    refine ⟨hinv, ?_, ?_⟩
    · have H := congrArg Real.exp htime
      rw [Real.exp_log (hw _ ht), Real.exp_add, Real.exp_log (hw s hs)] at H
      exact H.trans (mul_comm _ _)
    · have H := (hβ _ ht).scomp z hinv
      convert! H using 1
      ext i
      change (connectionClockRate (β (e.symm z)))⁻¹ * projectiveField (β (e.symm z)) i =
        (1 / (a (e.symm z) * connectionClockRate (β (e.symm z)))) *
          (a (e.symm z) * projectiveField (β (e.symm z)) i)
      field_simp [ne_of_gt (hapos _ ht), ne_of_gt (hD _ ht)]
