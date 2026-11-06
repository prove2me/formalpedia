-- Prove2me | solution 1 for BianchiIX.exists_projective_normalized_reparametrization
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:35:25.088199+00:00
-- url     : https://prove2.me/submissions/2b119355-28e0-4ff3-ad42-ceba815687b0

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_convex_positiveIntegralClock_target
import Theorems.Thm_BianchiIX_hasDerivAt_positiveIntegralClock_symm
import Theorems.Thm_BianchiIX_hasDerivAt_reparametrized_fromProjectiveState
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_positiveIntegralClock_symm_zero
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- Every solution of the exact projective system lifts to the maximal original flow. -/
theorem solution
    {β : ℝ → ProjectiveState} {I : Set ℝ} {s : ℝ}
    (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hβ : ∀ τ ∈ I, HasDerivAt β (projectiveField (β τ)) τ)
    (hD : ∀ τ ∈ I, 0 < projectiveStateDenom (β τ)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ τ, e τ = integralClock (fun u => projectiveStateDenom (β u) / 6) s τ) ∧
      e.target = integralClock (fun u => projectiveStateDenom (β u) / 6) s '' I ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧
      StrictMonoOn e I ∧
      e.target ⊆ normalizedMaxDomain (fromProjectiveState (β s)) 0 ∧
      (∀ t ∈ e.target,
        fromProjectiveState (β (e.symm t)) =
          normalizedMaxCurve (fromProjectiveState (β s)) 0 t ∧
        toProjectiveState (normalizedMaxCurve (fromProjectiveState (β s)) 0 t) = β (e.symm t)) := by
  let a : ℝ → ℝ := fun τ => projectiveStateDenom (β τ) / 6
  have ha : ContinuousOn a I := fun τ hτ =>
    ((continuous_projectiveStateDenom.continuousAt.comp (hβ τ hτ).continuousAt).div_const 6).continuousWithinAt
  have hpos : ∀ τ ∈ I, 0 < a τ := fun τ hτ => div_pos (hD τ hτ) (by norm_num)
  let e := positiveIntegralClock hI ho ha hs hpos
  have he0 : e s = 0 := integralClock_initial _ _
  have hzero : 0 ∈ e.target := he0 ▸ e.map_source hs
  have hinitial : e.symm 0 = s := positiveIntegralClock_symm_zero hI ho ha hs hpos
  have hconvex : Convex ℝ e.target := convex_positiveIntegralClock_target hI ho ha hs hpos
  have hsol (t : ℝ) (ht : t ∈ e.target) :
      HasDerivAt (fun u => fromProjectiveState (β (e.symm u)))
        (normalizedField (fromProjectiveState (β (e.symm t)))) t := by
    have hmem : e.symm t ∈ I := e.map_target ht
    have hc := hasDerivAt_positiveIntegralClock_symm hI ho ha hs hpos ht
    have hc' : HasDerivAt e.symm (6 / projectiveStateDenom (β (e.symm t))) t := by
      convert! hc using 1
      dsimp [a]
      field_simp
      rfl
    exact hasDerivAt_reparametrized_fromProjectiveState (hβ _ hmem)
      (ne_of_gt (hD _ hmem)) hc'
  let S : NormalizedSolution (fromProjectiveState (β s)) 0 :=
    { domain := e.target
      isOpen_domain := e.open_target
      convex_domain := hconvex
      initial_mem := hzero
      curve := fun t => fromProjectiveState (β (e.symm t))
      initial_eq := by rw [hinitial]
      hasDerivAt := hsol }
  refine ⟨e, rfl, fun _ => rfl, rfl, hconvex, hzero, hinitial,
    strictMonoOn_integralClock hI ho ha hs hpos, S.domain_subset_maximal, ?_⟩
  intro t ht
  have heq : fromProjectiveState (β (e.symm t)) =
      normalizedMaxCurve (fromProjectiveState (β s)) 0 t :=
    (normalizedMaxCurve_eqOn S ht).symm
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (hD _ (e.map_target ht)))
