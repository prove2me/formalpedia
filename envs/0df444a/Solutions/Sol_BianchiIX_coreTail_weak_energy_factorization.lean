-- Prove2me | solution 1 for BianchiIX.coreTail_weak_energy_factorization
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:12:10.16935+00:00
-- url     : https://prove2.me/submissions/275fe25c-1e88-4d33-806e-7b9239b44b1d

import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_normalizedProjectiveWallMultiplier_two
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedProjectiveWallMultiplier_formula
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

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
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailState_active {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    coreTailState η Y 2 = η := hvalid.1.1.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

end
end

private theorem BianchiIX.contDiffAt_coreTailWeakEnergyIntegrand_two {η t : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (H : coreTailValid η Y) (ht : t ∈ Icc 0 (coreTailTime η Y)) :
    ContDiffAt ℝ 2 coreTailWeakEnergyIntegrand (Y, t) := by
  let c := fun Z => fromProjectiveState (coreTailEntry Z)
  have hD := coreTailValid_denom_pos H
  have hc : ContDiffAt ℝ 2 c Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hk)
  have hp : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => (c p.1, p.2)) (Y, t) :=
    (hc.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hn := (contDiffAt_normalizedMaxCurve_two (H.2.1 t ht).1).comp (Y, t)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (f := fun p : CoreAngleState × ℝ => (c p.1, p.2)) hp
  have ha : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => normalizedProjectiveRate (c p.1) 0 p.2) (Y, t) :=
    contDiffAt_const.add (contDiffAt_pi.mp hn 0)
  have hy : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreTailEntry p.1) 0 p.2) (Y, t) :=
    (contDiffAt_toProjectiveState 2 (H.2.1 t ht).2.ne').comp (Y, t)
      (g := toProjectiveState) (f := fun p : CoreAngleState × ℝ => normalizedMaxCurve (c p.1) 0 p.2) hn
  have hb : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => normalizedProjectiveWallMultiplier (c p.1) p.2 2) (Y, t) :=
    (contDiffAt_normalizedProjectiveWallMultiplier_two
    (c := fun p : CoreAngleState × ℝ => c p.1) (τ := fun p => p.2) (Y := (Y, t))
    (hc.comp (Y, t) contDiffAt_fst) contDiffAt_snd ht.1
    (fun s hs => (H.2.1 s ⟨hs.1, hs.2.trans ht.2⟩).1)
    (fromProjectiveState_clock_pos hD) (H.2.1 t ht).2 2).1
  exact ((contDiffAt_const.mul ha).mul ((contDiffAt_pi.mp hy 0).sub contDiffAt_const)).mul (hb.pow 2)

/-- On the zero strong-wall plane, the exact finite-tail energy retains the initial weak-wall square. -/
theorem solution {η : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (H : coreTailValid η Y) (hu : Y 1 = 0) :
    coreRadius (coreTailState η Y 0) η ^ 2 =
      (Y 0) ^ 2 + (Y 2) ^ 2 * coreTailWeakEnergyCoefficient η Y := by
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime η Y
  let Z := projectiveOriginalFlow (coreTailEntry Y) 0
  let a := normalizedProjectiveRate x 0
  let B := fun t => normalizedProjectiveWallMultiplier x t 2
  have hD := coreTailValid_denom_pos H
  have hT : 0 ≤ T := H.1.1.1.le
  have hinit : Z 0 = coreTailEntry Y := projectiveOriginalFlow_initial hD 0
  have hZ (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt Z (a t • projectiveField (Z t)) t :=
    hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (H.2.1 t ht).1)
      (H.2.1 t ht).2.ne' ((normalizedMaxCurve_constraint (H.2.1 t ht).1).trans
        (fromProjectiveState_constraint hD.ne'))
  have hfactor (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 3) :
      Z t i.succ = coreTailEntry Y i.succ * normalizedProjectiveWallMultiplier x t i := by
    have HF := normalizedProjectiveWallMultiplier_formula (H.2.1 t ht).1
      (fromProjectiveState_clock_pos hD) (H.2.1 t ht).2 i
    rw [toProjectiveState_fromProjectiveState hD.ne'] at HF
    exact HF
  have hU (t : ℝ) (ht : t ∈ Icc 0 T) : Z t 1 = 0 := by
    have HF := hfactor t ht 0
    change Z t 1 = Y 1 * _ at HF
    simpa only [hu, zero_mul] using HF
  have hW (t : ℝ) (ht : t ∈ Icc 0 T) : Z t 3 = Y 2 * B t := hfactor t ht 2
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt (fun s => coreEnergy (Z s 0) (Z s 2))
        ((Y 2) ^ 2 * coreTailWeakEnergyIntegrand (Y, t)) t := by
    convert! (((hasDerivAt_pi.mp (hZ t ht) 0).sub_const 1).pow 2).add
      ((hasDerivAt_pi.mp (hZ t ht) 2).pow 2) using 1
    change (Y 2) ^ 2 * (2 * a t * (Z t 0 - 1) * B t ^ 2) =
      2 * (Z t 0 - 1) ^ (2 - 1) * (a t * phaseVelocity (Z t 0) (Z t 1) (Z t 2) (Z t 3)) +
        2 * (Z t 2) ^ (2 - 1) * (a t * activeVelocity (Z t 0) (Z t 1) (Z t 2) (Z t 3))
    rw [hU t ht, hW t ht]
    unfold phaseVelocity activeVelocity coupling
    ring
  have hic : ContinuousOn (fun t => coreTailWeakEnergyIntegrand (Y, t)) (Icc 0 T) := by
    intro t ht
    exact ((contDiffAt_coreTailWeakEnergyIntegrand_two hk H ht).continuousAt.comp
      (by fun_prop : ContinuousAt (fun s : ℝ => (Y, s)) t)).continuousWithinAt
  have hi : IntervalIntegrable (fun t => coreTailWeakEnergyIntegrand (Y, t)) volume 0 T :=
    hic.intervalIntegrable_of_Icc hT
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (uIcc_of_le hT ▸ ht)) (hi.const_mul ((Y 2) ^ 2))
  rw [intervalIntegral.integral_const_mul, hinit] at he
  have he0 : coreEnergy (coreTailEntry Y 0) (coreTailEntry Y 2) = (Y 0) ^ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ (Y 0) ^ 2 - 1 by nlinarith only [hk])
    dsimp [coreEnergy, coreTailEntry]
    nlinarith only [hs]
  rw [he0] at he
  change (Y 2) ^ 2 * coreTailWeakEnergyCoefficient η Y =
    coreEnergy (coreTailState η Y 0) (coreTailState η Y 2) - (Y 0) ^ 2 at he
  rw [coreTailState_active H] at he
  rw [coreRadius_sq]
  linarith only [he]
