-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_tangent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:58:30.695323+00:00
-- url     : https://prove2.me/submissions/a90d5c7a-4047-40b3-b8a3-72fdb2b2bc65

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_exists_compact_connection_coordinate_bounds
import Theorems.Thm_BianchiIX_exists_compact_tail_multiplier_bounds
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
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Positivity

noncomputable section
open BianchiIX
open Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_wall_product_direction_bound {x m a l C : ℝ} (hx : 0 < x) (hm : 0 < m)
    (ha : |a| ≤ Real.sqrt x) (hl : |l| ≤ C) :
    |m * (a + x * l)| ≤ x * m * (C + 1 / Real.sqrt x) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hid : x / Real.sqrt x = Real.sqrt x := (div_eq_iff hs).mpr (Real.mul_self_sqrt hx.le).symm
  rw [abs_mul, abs_of_pos hm]
  calc
    _ ≤ m * (|a| + |x * l|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hm.le
    _ = m * (|a| + x * |l|) := by rw [abs_mul, abs_of_pos hx]
    _ ≤ m * (Real.sqrt x + x * C) := mul_le_mul_of_nonneg_left
      (add_le_add ha (mul_le_mul_of_nonneg_left hl hx.le)) hm.le
    _ = m * (x / Real.sqrt x + x * C) := by rw [hid]
    _ = _ := by ring

end
end

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

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_compactConnectionCoordinates_two {η : ℝ} {Y : CoreAngleState}
    (hF : ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y)
    (hB : ∀ i : Fin 2, ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y) :
    ContDiffAt ℝ 2 (compactConnectionCoordinates η) Y := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hF
  · exact (by fun_prop : ContDiffAt ℝ 2 (fun Z : CoreAngleState => Z 1) Y).mul (hB 0)
  · exact (by fun_prop : ContDiffAt ℝ 2 (fun Z : CoreAngleState => Z 2) Y).mul (hB 1)
  · exact contDiffAt_const

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.compactConnectionCoordinates_fderiv {η : ℝ} {Y : CoreAngleState}
    (hF : ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y)
    (hB : ∀ i : Fin 2, ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y) (v : CoreAngleState) :
    fderiv ℝ (compactConnectionCoordinates η) Y v =
      ![fderiv ℝ (compactConnectionFinitePhase η) Y v,
        v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v,
        v 2 * coreTailMultiplier η Y 1 + Y 2 * fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y v, 0] := by
  have h := ((contDiffAt_compactConnectionCoordinates_two hF hB).differentiableAt (by norm_num)).hasFDerivAt
  have hc (i : Fin 4) := (hasFDerivAt_apply (𝕜 := ℝ) i (compactConnectionCoordinates η Y)).comp Y h
  ext i
  fin_cases i
  · exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
      ((hc 0).unique ((hF.differentiableAt (by norm_num)).hasFDerivAt))
  · have H := (hc 1).unique ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) Y).mul
      (((hB 0).differentiableAt (by norm_num)).hasFDerivAt))
    have H' := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H
    change fderiv ℝ (compactConnectionCoordinates η) Y v 1 =
      v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, add_apply,
      smul_apply, smul_eq_mul, mul_comm, add_comm] using H'
  · have H := (hc 2).unique ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) Y).mul
      (((hB 1).differentiableAt (by norm_num)).hasFDerivAt))
    have H' := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H
    change fderiv ℝ (compactConnectionCoordinates η) Y v 2 =
      v 2 * coreTailMultiplier η Y 1 + Y 2 * fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, add_apply,
      smul_apply, smul_eq_mul, mul_comm, add_comm] using H'
  · exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
      ((hc 3).unique (hasFDerivAt_const η Y))

end
end

private theorem BianchiIX.coreTailMultiplier_fderiv_log {η : ℝ} {Y : CoreAngleState} (i : Fin 2)
    (hB : DifferentiableAt ℝ (fun Z => coreTailMultiplier η Z i) Y) (v : CoreAngleState) :
    fderiv ℝ (fun Z => coreTailMultiplier η Z i) Y v = coreTailMultiplier η Y i *
      fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y v := by
  rw [(hB.hasFDerivAt.log (coreTailMultiplier_pos η Y i).ne').fderiv]
  simp only [smul_apply, smul_eq_mul]
  field_simp [(coreTailMultiplier_pos η Y i).ne']


/-- Finite-tail coordinates preserve the factors needed by the long-entrance logarithmic columns. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ A : ℝ, 1 ≤ A ∧ ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      (∀ᶠ Z in 𝓝 Y, coreTailValid η Z) ∧ ContDiffAt ℝ 2 (compactConnectionCoordinates η) Y ∧
        -Real.log (compactConnectionCoordinates η Y 2) ≤ A + |Real.log (Y 2)| ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ (compactConnectionCoordinates η) Y v
        |d 0| ≤ A ∧ |d 1| ≤ A ∧
          |d 1| ≤ compactConnectionCoordinates η Y 1 * (A + 1 / Real.sqrt (Y 1)) ∧
          |d 2| ≤ compactConnectionCoordinates η Y 2 * (A + 1 / Real.sqrt (Y 2)) ∧ d 3 = 0 := by
  obtain ⟨εc, hεc, R, hR, HC⟩ := exists_compact_connection_coordinate_bounds hη
  obtain ⟨εm, hεm, M, hM, HM⟩ := exists_compact_tail_multiplier_bounds ⟨hη.1, by linarith [hη.2]⟩
  let ε := min εc (min εm 1)
  let A := 2 * R + M + 1
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hRA : R ≤ A := by dsimp only [A]; linarith only [hR, hM]
  have h2RA : 2 * R ≤ A := by dsimp only [A]; linarith only [hM]
  have hMA : M ≤ A := by dsimp only [A]; linarith only [hR]
  have hεc' : ε ≤ εc := min_le_left _ _
  have hεm' : ε ≤ εm := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, lt_min hεc (lt_min hεm zero_lt_one), A, by dsimp only [A]; linarith only [hR, hM], ?_⟩
  intro Y hk hu hw
  obtain ⟨hvalid, hF, hDF, hBi⟩ := HC Y hk
    (by rw [abs_of_pos hu.1]; exact hu.2.trans hεc')
    (by rw [abs_of_pos hw.1]; exact hw.2.trans hεc')
  obtain ⟨_, _, _, _, hBm⟩ := HM Y hk
    (by rw [abs_of_pos hu.1]; exact hu.2.trans hεm')
    (by rw [abs_of_pos hw.1]; exact hw.2.trans hεm')
  have hmb (i : Fin 2) : (coreTailMultiplier η Y i)⁻¹ ≤ M ∧
      ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ ≤ M := by
    have H := (hBm i).2.2.2
    constructor <;> linarith only [H, (hBm i).1,
      inv_nonneg.mpr (hBm i).1.le,
      norm_nonneg (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y)]
  refine ⟨hvalid, contDiffAt_compactConnectionCoordinates_two hF (fun i => (hBi i).1), ?_, ?_⟩
  · change -Real.log (Y 2 * coreTailMultiplier η Y 1) ≤ _
    rw [Real.log_mul hw.1.ne' (hBi 1).2.1.ne']
    have H := Real.neg_inv_le_log (hBi 1).2.1.le
    linarith only [H, (hmb 1).1, hMA, neg_le_abs (Real.log (Y 2))]
  · intro v hv0 hv1 hv2
    have hvnorm : ‖v‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      fin_cases i
      · simp [hv0]
      · exact hv1.trans (Real.sqrt_le_one.mpr (hu.2.trans hε1))
      · exact hv2.trans (Real.sqrt_le_one.mpr (hw.2.trans hε1))
    have hnorm (L : CoreAngleState →L[ℝ] ℝ) : |L v| ≤ ‖L‖ := by
      exact (L.le_opNorm v).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hvnorm (norm_nonneg L))
    have hl (i : Fin 2) : |fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y v| ≤ A :=
      (hnorm _).trans ((hmb i).2.trans hMA)
    dsimp only
    rw [compactConnectionCoordinates_fderiv hF (fun i => (hBi i).1)]
    change |fderiv ℝ (compactConnectionFinitePhase η) Y v| ≤ A ∧
      |v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| ≤ A ∧ _
    refine ⟨(hnorm _).trans (hDF.trans hRA), ?_, ?_, ?_, rfl⟩
    · have H1 : |v 1| ≤ 1 := hv1.trans (Real.sqrt_le_one.mpr (hu.2.trans hε1))
      have H2 : |fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| ≤ R := (hnorm _).trans (hBi 0).2.2.2
      calc
        _ ≤ |v 1 * coreTailMultiplier η Y 0| + |Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| := abs_add_le _ _
        _ = |v 1| * coreTailMultiplier η Y 0 + Y 1 * |fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| := by
          rw [abs_mul, abs_mul, abs_of_pos (hBi 0).2.1, abs_of_pos hu.1]
        _ ≤ 1 * R + 1 * R := add_le_add
          (mul_le_mul H1 (hBi 0).2.2.1 (hBi 0).2.1.le zero_le_one)
          (mul_le_mul (hu.2.trans hε1) H2 (abs_nonneg _) zero_le_one)
        _ ≤ A := by linarith only [h2RA]
    · change |v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| ≤
        (Y 1 * coreTailMultiplier η Y 0) * (A + 1 / Real.sqrt (Y 1))
      rw [coreTailMultiplier_fderiv_log 0 ((hBi 0).1.differentiableAt (by norm_num))]
      convert sqrt_wall_product_direction_bound hu.1 (hBi 0).2.1 hv1 (hl 0) using 1
      congr 1
      ring
    · change |v 2 * coreTailMultiplier η Y 1 + Y 2 * fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y v| ≤
        (Y 2 * coreTailMultiplier η Y 1) * (A + 1 / Real.sqrt (Y 2))
      rw [coreTailMultiplier_fderiv_log 1 ((hBi 1).1.differentiableAt (by norm_num))]
      convert sqrt_wall_product_direction_bound hw.1 (hBi 1).2.1 hv2 (hl 1) using 1
      congr 1
      ring
