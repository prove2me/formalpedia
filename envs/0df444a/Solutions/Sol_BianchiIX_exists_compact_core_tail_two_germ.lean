-- Prove2me | solution 1 for BianchiIX.exists_compact_core_tail_two_germ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:02:37.904957+00:00
-- url     : https://prove2.me/submissions/18f9d971-3107-4851-aee9-e9bcc01e926b

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_coreTail_reference_regular
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

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology


/-- A fixed tail height gives one wall neighborhood and uniform bounds on each compact phase range. -/
theorem solution {a b η : ℝ} (ha : 1 < a) (hη : 0 < η ∧ η < 1) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (a ≤ Y 0 ∧ Y 0 ≤ b) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧
        |coreTailTime η Y| + ‖coreTailState η Y‖ +
          ‖fderiv ℝ (coreTailTime η) Y‖ + ‖fderiv ℝ (coreTailState η) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailTime η)) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailState η)) Y‖ ≤ C ∧
        (∀ᶠ Z in 𝓝 Y, coreTailValid η Z ∧ ContDiffAt ℝ 2 (coreTailTime η) Z ∧
          ContDiffAt ℝ 2 (coreTailState η) Z) := by
  let T := coreTailTime η
  let P := coreTailState η
  let G : Set CoreAngleState := {Y | coreTailValid η Y ∧ ContDiffAt ℝ 2 T Y ∧ ContDiffAt ℝ 2 P Y}
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc a b
  have hcS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    obtain ⟨_, _, ht, hP, hvalid⟩ := coreTail_reference_regular (ha.trans_le hk.1) hη
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hvalid, ht.eventually (by norm_num), hP.eventually (by norm_num)] with Z hz htZ hPZ
    exact ⟨hz, htZ, hPZ⟩
  obtain ⟨ε, hε, hεG⟩ := hcS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  let q : CoreAngleState → ℝ := fun Y => |T Y| + ‖P Y‖ + ‖fderiv ℝ T Y‖ +
    ‖fderiv ℝ P Y‖ + ‖fderiv ℝ (fderiv ℝ T) Y‖ + ‖fderiv ℝ (fderiv ℝ P) Y‖
  have hcq : ContinuousOn q W := by
    intro Y hY
    obtain ⟨_, ht, hP⟩ := hWG hY
    have ht' := ht.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hP' := hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact (((((ht.continuousAt.abs.add hP.continuousAt.norm).add
      (ht.continuousAt_fderiv (by norm_num)).norm).add
      (hP.continuousAt_fderiv (by norm_num)).norm).add
      (ht'.continuousAt_fderiv (by norm_num)).norm).add
      (hP'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hcS.cthickening.exists_bound_of_continuousOn hcq
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ε := by
    apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hu
    · simpa [Real.dist_eq] using hw
  have hYS : (![Y 0, 0, 0] : CoreAngleState) ∈ S := ⟨Y 0, hk, rfl⟩
  have hYW : Y ∈ W := mem_cthickening_of_dist_le Y _ ε S hYS hdist
  obtain ⟨hvalid, ht, hP⟩ := hWG hYW
  exact ⟨hvalid, ht, hP, (le_abs_self (q Y)).trans ((hB Y hYW).trans (le_max_left _ _)),
    mem_interior_iff_mem_nhds.mp (hεG hYW)⟩
