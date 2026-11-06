-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_return
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:27:50.17332+00:00
-- url     : https://prove2.me/submissions/8a7148a3-5045-496e-b1df-2cfe687b1c90

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Theorems.Thm_BianchiIX_compactConnection_actual_passage
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_compact_decay
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entranceReturn_walls_pos
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_compact_connection_entrance_data
import Theorems.Thm_BianchiIX_rpow_gain_bound
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrance_initial_denom_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : 0 < projectiveStateDenom y := by
  have hr : |coreRadius (y 0) (y 2) - coreRadius (y 0) (y 2)| ≤ coreRadius (y 0) (y 2) / 100 := by
    rw [sub_self, abs_zero]
    linarith
  exact (entrance_denom_bounds hk (entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2.le⟩)
    hu ⟨hv.1.le, hv.2.le⟩ hw).1

end
end

/-- The existence and amplitude assertions of (B.44), for the exact composed first arrival. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionTime η) Y ∧
        ContDiffAt ℝ 2 (compactConnectionState η) Y ∧
        compactConnectionState η Y = projectiveReflection
          (projectiveOriginalFlow (coreTailEntry Y) 0 (compactConnectionTime η Y)) ∧
        IsLeast {t : ℝ | 0 < t ∧ projectiveReflection
          (projectiveOriginalFlow (coreTailEntry Y) 0 t) 2 = 1} (compactConnectionTime η Y) ∧
        1 < compactConnectionState η Y 0 ∧ compactConnectionState η Y 2 = 1 ∧
        (0 < compactConnectionState η Y 1 ∧
          compactConnectionState η Y 1 ≤ C * Y 1 * (Y 2) ^ (19 / 12 : ℝ) ∧
          compactConnectionState η Y 1 ≤ Y 1) ∧
        (0 < compactConnectionState η Y 3 ∧
          compactConnectionState η Y 3 ≤ C * (Y 2) ^ (13 / 9 : ℝ) ∧
          compactConnectionState η Y 3 ≤ Y 2) := by
  obtain ⟨ε₀, hε₀, A, hA, HA⟩ := exists_compact_connection_entrance_data
    (δ := 1 / 10000) (by norm_num) hη
  let C := A * A ^ (19 / 12 : ℝ) + η * A ^ (13 / 9 : ℝ)
  have hC : 0 < C := add_pos (mul_pos hA (Real.rpow_pos_of_pos hA _))
    (mul_pos hη.1 (Real.rpow_pos_of_pos hA _))
  have hCA : A * A ^ (19 / 12 : ℝ) ≤ C := le_add_of_nonneg_right (by positivity [hη.1])
  have hCB : η * A ^ (13 / 9 : ℝ) ≤ C := le_add_of_nonneg_left (by positivity)
  obtain ⟨ε, hε, hε₀', hbudget⟩ := exists_common_rpow_budget (ι := Fin 2) Finset.univ
    (C := fun _ => C) (p := ![19 / 12, 4 / 9]) (ε := fun _ => 1)
    (fun _ _ => hC.le) (by intro i _; fin_cases i <;> norm_num) (by intros; norm_num) hε₀
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, htime, hentry, hradius, hm, hU, hV, hW, hUA, hVA⟩ :=
    HA Y hk ⟨hu.1, hu.2.trans hε₀'.le⟩ ⟨hw.1, hw.2.trans hε₀'.le⟩
  let y := compactConnectionEntry η Y
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨hV.1, by linarith only [hV.2]⟩
  have hw' : 0 < y 3 ∧ y 3 ≤ 1 / 10000 := by
    change 0 < compactConnectionEntry η Y 3 ∧ compactConnectionEntry η Y 3 ≤ 1 / 10000
    rw [hW]
    exact hη
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hU.1.le, hU.2⟩
  have hw'' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw'.1.le, hw'.2⟩
  have HR := entranceReturn_regular hradius.1 hm hu' hv hw''
  have hD := entrance_initial_denom_pos hradius.1 hm hu' hv hw''
  have hp := compactConnection_actual_passage htail hD HR.1
  have htime' : ContDiffAt ℝ 2 (compactConnectionTime η) Y :=
    (HR.2.1.comp Y hentry).add htime
  have hstate : ContDiffAt ℝ 2 (compactConnectionState η) Y := HR.2.2.1.comp Y hentry
  have hpos := entranceReturn_walls_pos hradius.1 hm hU hv hw'
    (entranceReturnTime y) ⟨HR.1.1.1.1.le, le_rfl⟩
  have hphase := entranceRegion_phase hradius.1
    (entranceReturn_region hradius.1 hm hu' hv hw'' (entranceReturnTime y) ⟨HR.1.1.1.1.le, le_rfl⟩)
  change 4 / 5 * coreRadius (y 0) (y 2) ≤ compactConnectionState η Y 0 - 1 ∧ _ at hphase
  have hdec := entranceReturn_compact_decay hradius.1 hradius.2.le hm hu' hv hw''
  have hUb : compactConnectionState η Y 1 ≤ (A * A ^ (19 / 12 : ℝ)) * Y 1 * (Y 2) ^ (19 / 12 : ℝ) := by
    calc
      _ ≤ y 1 * (y 2) ^ (19 / 12 : ℝ) := hdec.1
      _ ≤ (A * Y 1) * (A * Y 2) ^ (19 / 12 : ℝ) :=
        mul_le_mul hUA (Real.rpow_le_rpow hv.1.le hVA (by norm_num))
          (Real.rpow_nonneg hv.1.le _) (mul_nonneg hA.le hu.1.le)
      _ = _ := by rw [Real.mul_rpow hA.le hw.1.le]; ring
  have hWb : compactConnectionState η Y 3 ≤ (η * A ^ (13 / 9 : ℝ)) * (Y 2) ^ (13 / 9 : ℝ) := by
    calc
      _ ≤ η * (y 2) ^ (13 / 9 : ℝ) := by
        simpa only [compactConnectionState, y, hW] using hdec.2
      _ ≤ η * (A * Y 2) ^ (13 / 9 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv.1.le hVA (by norm_num)) hη.1.le
      _ = _ := by rw [Real.mul_rpow hA.le hw.1.le]; ring
  have hUfinal : compactConnectionState η Y 1 ≤ C * Y 1 * (Y 2) ^ (19 / 12 : ℝ) :=
    hUb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA hu.1.le)
      (Real.rpow_nonneg hw.1.le _))
  have hWfinal : compactConnectionState η Y 3 ≤ C * (Y 2) ^ (13 / 9 : ℝ) :=
    hWb.trans (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg hw.1.le _))
  have hUbgt : C * (Y 2) ^ (19 / 12 : ℝ) ≤ 1 :=
    (hbudget (Y 2) hw 0 (Finset.mem_univ _)).le
  have hWbgt : C * (Y 2) ^ (4 / 9 : ℝ) ≤ 1 :=
    (hbudget (Y 2) hw 1 (Finset.mem_univ _)).le
  have hWgain : C * (Y 2) ^ (13 / 9 : ℝ) ≤ Y 2 := by
    have H := rpow_gain_bound (C := C) (p := 13 / 9) (q := 1) hw.1 le_rfl hC.le (by norm_num)
      (by norm_num; exact hWbgt)
    simpa only [Real.rpow_one] using H
  refine ⟨htail, HR.1, htime', hstate, hp.1, hp.2, ?_,
    (entranceReturn_active_component hradius.1 hm hu' hv hw'').1,
    ⟨hpos.1, hUfinal, ?_⟩, ⟨hpos.2.2, hWfinal, hWfinal.trans hWgain⟩⟩
  · have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hradius.1]
    nlinarith only [hk0, hphase.1]
  · exact hUfinal.trans (by
      simpa only [mul_right_comm, one_mul] using mul_le_mul_of_nonneg_right hUbgt hu.1.le)
