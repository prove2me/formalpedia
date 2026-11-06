-- Prove2me | solution 1 for BianchiIX.exists_compact_tail_multiplier_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:03:52.126755+00:00
-- url     : https://prove2.me/submissions/e7cc6cac-8ef7-4a0c-bf35-8e1a45b074f6

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Theorems.Thm_BianchiIX_contDiffAt_coreTailMultiplier_two
import Theorems.Thm_BianchiIX_coreTail_reflected_multiplier_state
import Theorems.Thm_BianchiIX_exists_compact_connection_tail
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
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalizedProjectiveWallMultiplier_pos (x : NormalizedState) (T : ℝ) (i : Fin 3) :
    0 < normalizedProjectiveWallMultiplier x T i := Real.exp_pos _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailMultiplier_pos (η : ℝ) (Y : CoreAngleState) (i : Fin 2) :
    0 < coreTailMultiplier η Y i := normalizedProjectiveWallMultiplier_pos _ _ _

end
end

/-- B.45 with actual positive factors, bounded inverses, and two bounded logarithmic derivatives. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧
        projectiveReflection (coreTailState η Y) =
          ![-coreTailState η Y 0, Y 1 * coreTailMultiplier η Y 0, Y 2 * coreTailMultiplier η Y 1, η] ∧
        ∀ i : Fin 2, 0 < coreTailMultiplier η Y i ∧
          ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y ∧
          coreTailMultiplier η Y i + (coreTailMultiplier η Y i)⁻¹ +
            ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ +
            ‖fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y‖ ≤ C := by
  obtain ⟨ε, hε, _, _, Htail⟩ := exists_compact_connection_tail hη
  let S : Set CoreAngleState := Icc (![31 / 8, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcompact : IsCompact S := isCompact_Icc
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩, abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hreg {Y : CoreAngleState} (hY : Y ∈ S) (i : Fin 2) :
      ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
        ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y := by
    have hbox := hcoords hY
    have HY := Htail Y hbox.1 hbox.2.1 hbox.2.2
    exact contDiffAt_coreTailMultiplier_two (by linarith only [hbox.1.1]) HY.1 HY.2.1 i
  let q : CoreAngleState → Fin 2 → ℝ := fun Y i =>
    coreTailMultiplier η Y i + (coreTailMultiplier η Y i)⁻¹ +
      ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ +
      ‖fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y‖
  have hcq (i : Fin 2) : ContinuousOn (fun Y => q Y i) S := by
    intro Y hY
    obtain ⟨hb, hl⟩ := hreg hY i
    have hl' := hl.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact (((hb.continuousAt.add (hb.inv (coreTailMultiplier_pos η Y i).ne').continuousAt).add
      (hl.continuousAt_fderiv (by norm_num)).norm).add
      (hl'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  have hcmax : ContinuousOn (fun Y => max (q Y 0) (q Y 1)) S :=
    (continuous_fst.max continuous_snd).comp_continuousOn ((hcq 0).prodMk (hcq 1))
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcmax
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hY : Y ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hk.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have HY := Htail Y hk hu hw
  refine ⟨HY.1, HY.2.1, HY.2.2.1, coreTail_reflected_multiplier_state HY.1, ?_⟩
  intro i
  refine ⟨coreTailMultiplier_pos η Y i, (hreg hY i).1, (hreg hY i).2, ?_⟩
  have H : max (q Y 0) (q Y 1) ≤ max B 1 :=
    (le_abs_self _).trans ((hB Y hY).trans (le_max_left _ _))
  fin_cases i
  · exact (le_max_left _ _).trans H
  · exact (le_max_right _ _).trans H
