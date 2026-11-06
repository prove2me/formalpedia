-- Prove2me | solution 1 for BianchiIX.referenceEntrance_return
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:07:28.545615+00:00
-- url     : https://prove2.me/submissions/6765aa99-f368-427d-bcab-e6e6c9edeb34

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_exists_projective_normalized_reparametrization
import Theorems.Thm_BianchiIX_hasDerivAt_referenceClockPrimitive
import Theorems.Thm_BianchiIX_hasDerivAt_referencePulse
import Theorems.Thm_BianchiIX_referenceHalfTime_pos
import Theorems.Thm_BianchiIX_referencePulse_clock_integral
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_energy
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_height_exit
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.referenceShiftClock_initial (k s : ℝ) : referenceShiftClock k s s = 0 := sub_self _

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
open Set

private theorem BianchiIX.referenceShiftClock_normalized_orbit (k s t : ℝ) :
    referenceShiftClock k s t ∈ normalizedMaxDomain (fromProjectiveState (referencePulse k s)) 0 ∧
      normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0 (referenceShiftClock k s t) =
        fromProjectiveState (referencePulse k t) := by
  obtain ⟨e, hsrc, he, _, _, _, _, _, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := s) convex_univ isOpen_univ (mem_univ _)
      (fun u _ => hasDerivAt_referencePulse k u) (fun u _ => referencePulse_denom_pos k u)
  have hmem : t ∈ e.source := by rw [hsrc]; trivial
  have ht : e t = referenceShiftClock k s t := by rw [he, referencePulse_clock_integral]; rfl
  have htarget : referenceShiftClock k s t ∈ e.target := ht ▸ e.map_source hmem
  have hinv : e.symm (referenceShiftClock k s t) = t := by rw [← ht, e.left_inv hmem]
  refine ⟨hdom htarget, ?_⟩
  have H := (hflow _ htarget).1
  rw [hinv] at H
  exact H.symm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceShiftClock_projective_orbit (k s t : ℝ) :
    projectiveOriginalFlow (referencePulse k s) 0 (referenceShiftClock k s t) = referencePulse k t := by
  unfold projectiveOriginalFlow
  rw [(referenceShiftClock_normalized_orbit k s t).2]
  exact toProjectiveState_fromProjectiveState (referencePulse_denom_pos k t).ne'

end
end

private theorem BianchiIX.referencePulse_height_entry {k v : ℝ} (hk : 0 < k) (hv : 0 < v ∧ v < k) :
    referencePulse k (-referenceHeightTime k v) = referenceEntranceState k v := by
  have H := referencePulse_height_exit hk hv
  have HM := congrFun H 0
  have HV := congrFun H 2
  change 1 - k * Real.tanh (k * referenceHeightTime k v) = 1 - Real.sqrt (k ^ 2 - v ^ 2) at HM
  change k / Real.cosh (k * referenceHeightTime k v) = v at HV
  ext i
  fin_cases i
  · dsimp [referencePulse, referenceEntranceState]
    rw [mul_neg, Real.tanh_neg]
    linarith only [HM]
  · rfl
  · change k / Real.cosh (k * (-referenceHeightTime k v)) = v
    rw [mul_neg, Real.cosh_neg]
    exact HV
  · rfl

private theorem BianchiIX.referencePulse_active_lt_one_before {k t : ℝ} (hk : 1 < k) (ht : t < -referenceHalfTime k) :
    referencePulse k t 2 < 1 := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hhalf : k * referenceHalfTime k = Real.arcosh k := by
    dsimp [referenceHalfTime]
    field_simp
  have ht0 : t < 0 := ht.trans (neg_neg_of_pos (referenceHalfTime_pos hk))
  have H := mul_lt_mul_of_pos_left ht hk0
  rw [mul_neg, hhalf] at H
  have hcosh : k < Real.cosh (k * t) := by
    calc
      k = Real.cosh (Real.arcosh k) := (Real.cosh_arcosh hk.le).symm
      _ < Real.cosh (k * t) := by
        apply Real.cosh_lt_cosh.mpr
        rw [abs_of_pos (Real.arcosh_pos hk), abs_of_neg (mul_neg_of_pos_of_neg hk0 ht0)]
        linarith only [H]
  exact (div_lt_one (Real.cosh_pos _)).mpr hcosh

private theorem BianchiIX.referenceEntrance_radius {k v : ℝ} (hk : 0 < k) (hv : 0 < v ∧ v < k) :
    coreRadius (referenceEntranceState k v 0) (referenceEntranceState k v 2) = k := by
  rw [← referencePulse_height_entry hk hv, coreRadius, referencePulse_energy, Real.sqrt_sq hk.le]


/-- The canonical first arrival agrees with the explicit upward reference segment. -/
theorem solution {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    entranceReturnTime (referenceEntranceState k v) =
        referenceShiftClock k (-referenceHeightTime k v) (-referenceHalfTime k) ∧
      entranceReturnState (referenceEntranceState k v) = referencePulse k (-referenceHalfTime k) := by
  let y := referenceEntranceState k v
  let s := -referenceHeightTime k v
  let t := -referenceHalfTime k
  let T := referenceShiftClock k s t
  have hk0 : 0 < k := by linarith
  have hk1 : 1 < k := by linarith
  have hentry : referencePulse k s = y := referencePulse_height_entry hk0 ⟨hv.1, hv.2.trans hk1⟩
  have hR : coreRadius (y 0) (y 2) = k := referenceEntrance_radius hk0 ⟨hv.1, hv.2.trans hk1⟩
  have hm : 1 ≤ y 0 := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hvalid := (entranceReturn_regular (by rw [hR]; exact hk) hm hu hv hw).1
  have hst : s < t := neg_lt_neg (referenceHalfTime_lt_heightTime hk1 hv)
  have hT : 0 < T := by
    have H := referenceShiftClock_strictMono k s hst
    simpa only [referenceShiftClock_initial] using H
  have horbit (r : ℝ) : projectiveOriginalFlow y 0 (referenceShiftClock k s r) = referencePulse k r := by
    rw [← hentry]
    exact referenceShiftClock_projective_orbit k s r
  have hdom : T ∈ normalizedMaxDomain (fromProjectiveState y) 0 := by
    rw [← hentry]
    exact (referenceShiftClock_normalized_orbit k s t).1
  have hhit : projectiveActiveWall (normalizedMaxCurve (fromProjectiveState y) 0 T) = 1 := by
    change projectiveOriginalFlow y 0 T 2 = 1
    rw [horbit, referencePulse_entry hk1]
    rfl
  have hle : entranceReturnTime y ≤ T := hvalid.1.2 ⟨hT, hdom, hhit⟩
  have hclock : Continuous (referenceShiftClock k s) :=
    continuous_iff_continuousAt.mpr fun r => (hasDerivAt_referenceShiftClock k s r).continuousAt
  have hmem : entranceReturnTime y ∈ Icc (referenceShiftClock k s s) (referenceShiftClock k s t) := by
    rw [referenceShiftClock_initial]
    exact ⟨hvalid.1.1.1.le, hle⟩
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hst.le hclock.continuousOn hmem
  have hrhit : referencePulse k r 2 = 1 := by
    rw [← horbit, he]
    exact hvalid.1.1.2.2
  have hrt : r = t := by
    by_contra hn
    have H := referencePulse_active_lt_one_before hk1 (lt_of_le_of_ne hr.2 hn)
    rw [hrhit] at H
    exact lt_irrefl _ H
  have htime : entranceReturnTime y = T := by rw [hrt] at he; exact he.symm
  refine ⟨htime, ?_⟩
  change projectiveOriginalFlow y 0 (entranceReturnTime y) = referencePulse k t
  rw [htime, horbit]
