-- Prove2me | solution 1 for BianchiIX.exists_compact_core_factorization
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:42:52.700352+00:00
-- url     : https://prove2.me/submissions/2454c85b-cb1b-4e7c-a7ac-0c38f912aae2

import Definitions.Def_BianchiIX_Dynamics_CompactCoreFactors
import Theorems.Thm_BianchiIX_contDiffAt_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_coordinateFactor_identity
import Theorems.Thm_BianchiIX_coreRadiusReturn_wall_zero
import Theorems.Thm_BianchiIX_exists_compact_core_return_two_germ
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiff_coordinateSegment {n : ℕ} (i : Fin n) (m : WithTop ℕ∞) :
    ContDiff ℝ m (fun p : (Fin n → ℝ) × ℝ => coordinateSegment i p.1 p.2) := by
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simp only [coordinateSegment, Function.update_self]
    fun_prop
  · simp only [coordinateSegment, Function.update_of_ne h]
    fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_coordinateFactor {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {Y : Fin n → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (coordinateSegment i Y s)) :
    ContDiffAt ℝ 1 (coordinateFactor f i) Y := by
  apply contDiffAt_intervalIntegral_of_contDiffAt
    (F := fun p => fderiv ℝ f (coordinateSegment i p.1 p.2) (Pi.single i 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  intro s hs
  have hD := ((hf s hs).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp (Y, s)
    (contDiff_coordinateSegment i 1).contDiffAt
  exact hD.clm_apply contDiffAt_const

end
end

private theorem BianchiIX.coordinateSegment_core_box {Y : CoreAngleState} {ε s : ℝ} (i : Fin 2)
    (hs : 0 ≤ s ∧ s ≤ 1) (hu : |Y 1| ≤ ε) (hw : |Y 2| ≤ ε) :
    coordinateSegment i.succ Y s 0 = Y 0 ∧
      |coordinateSegment i.succ Y s 1| ≤ ε ∧ |coordinateSegment i.succ Y s 2| ≤ ε := by
  have H (a : ℝ) : |s * a| ≤ |a| := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hs.2
  fin_cases i
  · exact ⟨rfl, (H _).trans hu, hw⟩
  · exact ⟨rfl, hu, (H _).trans hw⟩

private theorem BianchiIX.eventually_compactCoreFactor_formula {Y : CoreAngleState} (i : Fin 2)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ Z in 𝓝 (coordinateSegment i.succ Y s),
      coreRadiusReturnValid Z ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Z) :
    ∀ᶠ Z in 𝓝 Y, coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i := by
  have H : ∀ᶠ Z in 𝓝 Y, ∀ s ∈ Icc (0 : ℝ) 1,
      coreRadiusReturnValid (coordinateSegment i.succ Z s) ∧
        ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) (coordinateSegment i.succ Z s) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have Hc : ContinuousAt (fun p : CoreAngleState × ℝ => coordinateSegment i.succ p.1 p.2) (Y, s) :=
      (contDiff_coordinateSegment i.succ 1).continuous.continuousAt
    exact Hc.eventually (hseg s hs)
  filter_upwards [H] with Z hZ
  have hc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := contDiffAt_pi.mp (hZ s hs).2 i.succ
  have hvalid : coreRadiusReturnValid (Function.update Z i.succ 0) := by
    simpa only [coordinateSegment, zero_mul] using (hZ 0 (by norm_num)).1
  have hzero := coreRadiusReturn_wall_zero hvalid i (Function.update_self _ _ _)
  have H' := coordinateFactor_identity hc
  rw [hzero, sub_zero] at H'
  exact H'

/-- Actual factorization and C1 factors on one fixed neighborhood, including both sides of zero walls. -/
theorem solution :
    ∃ ε > (0 : ℝ), ∀ Y : CoreAngleState, (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ∀ i : Fin 2, ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
          coreReturnState coreRadiusReturnTime Y i.succ = Y i.succ * compactCoreFactor Y i ∧
          (∀ᶠ Z in 𝓝 Y, coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i) := by
  obtain ⟨ε, hε, _, _, hbox⟩ := exists_compact_core_return_two_germ
  refine ⟨ε, hε, ?_⟩
  intro Y hk hu hw
  have hY := hbox Y hk hu hw
  refine ⟨hY.1, hY.2.2.1, ?_⟩
  intro i
  have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := coordinateSegment_core_box i hs hu hw
  have hf (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := hbox (coordinateSegment i.succ Y s)
    (by rw [(hseg s hs).1]; exact hk) (hseg s hs).2.1 (hseg s hs).2.2
  have hc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 2 (fun Z => coreReturnState coreRadiusReturnTime Z i.succ) (coordinateSegment i.succ Y s) :=
    contDiffAt_pi.mp (hf s hs).2.2.1 i.succ
  have hformula := eventually_compactCoreFactor_formula i (fun s hs =>
    ((hf s hs).2.2.2.2).mono fun _ h => ⟨h.1, h.2.2⟩)
  exact ⟨contDiffAt_coordinateFactor hc, hformula.self_of_nhds, hformula⟩
