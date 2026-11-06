-- Prove2me | solution 1 for BianchiIX.contDiffAt_normalizedProjectiveWallMultiplier_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:35:22.35271+00:00
-- url     : https://prove2.me/submissions/2691fa28-6b71-4a60-b061-e2daf296da95

import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Theorems.Thm_BianchiIX_contDiffAt_moving_intervalIntegral_two
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end

private theorem BianchiIX.contDiff_wallRate (n : WithTop ℕ∞) (i : Fin 3) : ContDiff ℝ n (wallRate i) := by
  change ContDiff ℝ n (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

/-- Parameter-dependent finite flights have positive C2 wall factors, including zero entrance walls. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → NormalizedState} {τ : E → ℝ} {Y : E}
    (hc : ContDiffAt ℝ 2 c Y) (hτ : ContDiffAt ℝ 2 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (c Y) 0)
    (hA0 : 0 < 1 + c Y 0) (hAT : 0 < 1 + normalizedMaxCurve (c Y) 0 (τ Y) 0) (i : Fin 3) :
    ContDiffAt ℝ 2 (fun Z => normalizedProjectiveWallMultiplier (c Z) (τ Z) i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (normalizedProjectiveWallMultiplier (c Z) (τ Z) i)) Y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) :
      ContDiffAt ℝ 2 (fun p : E × ℝ => wallRate i (normalizedMaxCurve (c p.1) 0 p.2)) (Y, t) := by
    have hp : ContDiffAt ℝ 2 (fun p : E × ℝ => (c p.1, p.2)) (Y, t) :=
      (hc.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
    have hflow := (contDiffAt_normalizedMaxCurve_two (hdom ht)).comp (Y, t) hp
    exact (contDiff_wallRate 2 i).contDiffAt.comp (Y, t) hflow
  have hInt := contDiffAt_moving_intervalIntegral_two hτ hpos hF
  have hEnd : ContDiffAt ℝ 2 (fun Z => normalizedMaxCurve (c Z) 0 (τ Z)) Y :=
    (contDiffAt_normalizedMaxCurve_two (hdom ⟨hpos, le_rfl⟩)).comp Y
      (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
      (f := fun Z => (c Z, τ Z)) (hc.prodMk hτ)
  have hStart : ContDiffAt ℝ 2 (fun Z => 1 + c Z 0) Y :=
    contDiffAt_const.add (contDiffAt_pi.mp hc 0)
  have hFinish : ContDiffAt ℝ 2 (fun Z => 1 + normalizedMaxCurve (c Z) 0 (τ Z) 0) Y :=
    contDiffAt_const.add (contDiffAt_pi.mp hEnd 0)
  have hLog := ((hStart.log hA0.ne').sub (hFinish.log hAT.ne')).add hInt
  refine ⟨hLog.exp, ?_⟩
  simpa only [normalizedProjectiveWallMultiplier, Real.log_exp] using hLog
