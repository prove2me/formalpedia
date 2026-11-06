-- Prove2me | solution 1 for BianchiIX.exists_reference_two_taub_visit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:07:18.551141+00:00
-- url     : https://prove2.me/submissions/39a27a76-8b51-40ca-872a-62e663e110ba

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_Dynamics_ReferenceActualVariation
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_referenceClockPrimitive
import Theorems.Thm_BianchiIX_referenceClock_normalized_orbit
import Theorems.Thm_BianchiIX_referenceHalfTime_pos
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_height_exit
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceHalfTime_lt_heightTime {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    referenceHalfTime k < referenceHeightTime k η := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  apply (div_lt_div_iff_of_pos_right hk0).mpr
  apply (Real.arcosh_lt_arcosh hk0 (div_pos hk0 hη.1)).mpr
  exact (lt_div_iff₀ hη.1).mpr (by nlinarith only [hk0, hη.2])

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_referenceShiftClock (k s t : ℝ) :
    HasDerivAt (referenceShiftClock k s) (projectiveStateDenom (referencePulse k t) / 6) t :=
  (hasDerivAt_referenceClockPrimitive k t).sub_const _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceShiftClock_strictMono (k s : ℝ) : StrictMono (referenceShiftClock k s) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_referenceShiftClock k s t).deriv]
  exact div_pos (referencePulse_denom_pos k t) (by norm_num)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_sq (x y : NormalizedState) :
    normalizedEuclideanDistance x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  simp [normalizedEuclideanDistance, EuclideanSpace.dist_sq_eq, Real.dist_eq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuous_normalizedEuclideanDistance :
    Continuous (fun p : NormalizedState × NormalizedState => normalizedEuclideanDistance p.1 p.2) := by
  unfold normalizedEuclideanDistance
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWall_taubDistance_sq (m v : ℝ) :
    normalizedEuclideanDistance (fromProjectiveState ![m, 0, v, 0]) (taubPoint 1) ^ 2 =
      3 * ((m + 1) ^ 2 + v ^ 2) / (3 + m ^ 2 + v ^ 2) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hD : 3 + m ^ 2 + v ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [normalizedEuclideanDistance_sq]
  simp [Fin.sum_univ_succ, fromProjectiveState, taubPoint,
    projectiveStateDenom, projectiveDenom, curvature]
  field_simp
  ring_nf
  simp only [hs, show Real.sqrt 3 ^ 4 = 9 by nlinarith [sq_nonneg (Real.sqrt 3 ^ 2 - 3)]]
  ring

end
end


/-- A finite point on the radius-two boundary orbit lies in any prescribed Taub neighborhood. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, T ∈ normalizedMaxDomain (referenceEntryState 2) 0 ∧
      normalizedEuclideanDistance (normalizedMaxCurve (referenceEntryState 2) 0 T) (taubPoint 1) < ε := by
  let y : ℝ → ProjectiveState := fun v => ![1 - Real.sqrt (4 - v ^ 2), 0, v, 0]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hy : Continuous y := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [y] <;> fun_prop
  have hD : projectiveStateDenom (y 0) ≠ 0 := by
    dsimp [y, projectiveStateDenom, projectiveDenom, curvature]
    norm_num [hs4]
  have hc := (contDiffAt_fromProjectiveState 0 hD).continuousAt.comp hy.continuousAt
  have hd := continuous_normalizedEuclideanDistance.continuousAt.comp
    (hc.prodMk (continuousAt_const (y := taubPoint 1)))
  have hz : normalizedEuclideanDistance (fromProjectiveState (y 0)) (taubPoint 1) = 0 := by
    have H := singleWall_taubDistance_sq (-1) 0
    have hy₀ : y 0 = ![-1, 0, 0, 0] := by norm_num [y, hs4]
    rw [hy₀]
    norm_num at H
    exact H
  have he : ∀ᶠ v in 𝓝 (0 : ℝ), normalizedEuclideanDistance (fromProjectiveState (y v)) (taubPoint 1) < ε :=
    hd.eventually (isOpen_Iio.mem_nhds (by simpa only [Function.comp_apply, hz, mem_Iio] using hε))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let v := min (r / 2) (1 / 2)
  have hv : 0 < v := lt_min (half_pos hr) (by norm_num)
  have hv1 : v < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hvr : v < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  have hnear := hball (show dist v 0 < r by simpa [Real.dist_eq, abs_of_pos hv] using hvr)
  let t := referenceHeightTime 2 v
  have ht : -referenceHalfTime 2 < t := by
    have H := referenceHalfTime_lt_heightTime (by norm_num : (1 : ℝ) < 2) ⟨hv, hv1⟩
    have Hp := referenceHalfTime_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [t]
    linarith only [H, Hp]
  have hT : 0 < referenceClock 2 t := by
    have H := referenceShiftClock_strictMono 2 (-referenceHalfTime 2) ht
    simpa only [referenceShiftClock, referenceClock, sub_self] using H
  refine ⟨referenceClock 2 t, hT, (referenceClock_normalized_orbit 2 t).1, ?_⟩
  rw [(referenceClock_normalized_orbit 2 t).2]
  have hp := referencePulse_height_exit (by norm_num : (0 : ℝ) < 2) ⟨hv, by linarith only [hv1]⟩
  change normalizedEuclideanDistance (fromProjectiveState (referencePulse 2 (referenceHeightTime 2 v))) _ < ε
  rw [hp]
  simpa only [y, show (2 : ℝ) ^ 2 = 4 by norm_num] using hnear
