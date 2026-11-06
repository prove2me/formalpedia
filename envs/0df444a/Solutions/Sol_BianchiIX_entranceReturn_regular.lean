-- Prove2me | solution 1 for BianchiIX.entranceReturn_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:10:58.269204+00:00
-- url     : https://prove2.me/submissions/8f2c1c66-09d2-4b54-91c2-a9cb669d4dd9

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_activeWall_first_upward_hit_two
import Theorems.Thm_BianchiIX_exists_normalized_entrance_first_arrival
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
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
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_speed_bounds {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    3 / 4 * k ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ 21 / 20 * k := by
  have hC := connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hm.1, hm.2, hC.1, hC.2, hu.2, hu2, hk]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_projective_wall_sign {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (β t i.succ = 0 ↔ β s i.succ = 0) ∧ (0 ≤ β t i.succ ↔ 0 ≤ β s i.succ) := by
  have H := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hh => hasDerivAt_normalizedMaxCurve hh) hs ht i
  exact ⟨(toProjectiveState_wall_sign hAt i).1.trans (H.1.trans (toProjectiveState_wall_sign hAs i).1.symm),
    (toProjectiveState_wall_sign hAt i).2.trans (H.2.trans (toProjectiveState_wall_sign hAs i).2.symm)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_projective_wall_pos {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) (hi : 0 < toProjectiveState (normalizedMaxCurve x t₀ s) i.succ) :
    0 < toProjectiveState (normalizedMaxCurve x t₀ t) i.succ := by
  have H := normalized_projective_wall_sign hs ht hAs hAt i
  have hne : toProjectiveState (normalizedMaxCurve x t₀ t) i.succ ≠ 0 :=
    fun h => (ne_of_gt hi) (H.1.mp h)
  exact lt_of_le_of_ne (H.2.mpr hi.le) hne.symm

end
end

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
open Set

private theorem BianchiIX.entranceRegion_speed {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    3 / 4 * k ≤ entranceClockRate y ∧ entranceClockRate y ≤ 21 / 20 * k :=
  entrance_speed_bounds hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_clock_pos {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    0 < entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]

end
end

private theorem BianchiIX.entrance_initial_denom_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : 0 < projectiveStateDenom y := by
  have hr : |coreRadius (y 0) (y 2) - coreRadius (y 0) (y 2)| ≤ coreRadius (y 0) (y 2) / 100 := by
    rw [sub_self, abs_zero]
    linarith
  exact (entrance_denom_bounds hk (entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2.le⟩)
    hu ⟨hv.1.le, hv.2.le⟩ hw).1

/-- The actual first upward arrival is C2 in all four ordinary initial coordinates. -/
theorem solution {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let x := fromProjectiveState y
    let T := entranceReturnTime y
    entranceReturnValid y ∧ ContDiffAt ℝ 2 entranceReturnTime y ∧
      ContDiffAt ℝ 2 entranceReturnState y ∧
      HasFDerivAt entranceReturnTime
        ((normalizedEventTimeDifferential projectiveActiveWall x 0 T).comp
          (fderiv ℝ fromProjectiveState y)) y ∧
      HasFDerivAt entranceReturnState
        (((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
          (normalizedEventDifferential projectiveActiveWall x 0 T)).comp
          (fderiv ℝ fromProjectiveState y)) y ∧
      (∀ᶠ z in 𝓝 y, entranceReturnValid z) := by
  intro x T₀
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint hD.ne'
  have hinit : toProjectiveState (normalizedMaxCurve x 0 0) = y := by
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState hD.ne'
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  obtain ⟨T, hT, hhit, _, hregion, _⟩ := exists_normalized_entrance_first_arrival hc hk le_rfl hA
    (by simpa only [hinit] using hm) (by simp only [hinit]) (by simpa only [hinit] using hu)
    (by simpa only [hinit] using hv) (by simpa only [hinit] using hw)
  have hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0 := by
    intro t ht
    have hK : 0 < coreRadius (y 0) (y 2) + 1 := by linarith
    exact ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1,
      lt_of_lt_of_le (by positivity) (hregion t ht).1⟩
  have hrate : ∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveActiveWall x 0 t := by
    intro t ht
    have hv0 : 0 < toProjectiveState (normalizedMaxCurve x 0 0) 2 := by rw [hinit]; exact hv.1
    have hvt := normalized_projective_wall_pos (hreg 0 ⟨le_rfl, hT.le⟩).1 (hreg t ht).1
      (hreg 0 ⟨le_rfl, hT.le⟩).2 (hreg t ht).2 1 hv0
    change 0 < fderiv ℝ projectiveActiveWall (normalizedMaxCurve x 0 t) (normalizedField (normalizedMaxCurve x 0 t))
    rw [projectiveActiveWall_fderiv_field (hreg t ht).2.ne'
      ((normalizedMaxCurve_constraint (hreg t ht).1).trans hc)]
    exact mul_pos (hreg t ht).2 (mul_pos (entranceRegion_clock_pos hk (hregion t ht).2) hvt)
  obtain ⟨τ, hτ, hcτ, hcP, hdτ, hdP, hnear⟩ := exists_activeWall_first_upward_hit_two hT hreg hrate hhit
  have hcI := contDiffAt_fromProjectiveState 2 hD.ne'
  have hnear' := hcI.continuousAt.eventually hnear
  have heq : entranceReturnTime =ᶠ[𝓝 y] (fun z => τ (fromProjectiveState z)) := by
    filter_upwards [hnear'] with z hz
    exact hz.1.csInf_eq
  have hT₀ : T₀ = T := heq.self_of_nhds.trans hτ
  have hnearValid : ∀ᶠ z in 𝓝 y, entranceReturnValid z := by
    filter_upwards [hnear', heq] with z hz htime
    dsimp only [entranceReturnValid]
    rw [htime]
    exact hz
  have hcTime : ContDiffAt ℝ 2 entranceReturnTime y :=
    (hcτ.comp y hcI).congr_of_eventuallyEq heq
  have heqP : entranceReturnState =ᶠ[𝓝 y]
      (fun z => toProjectiveState (normalizedMaxCurve (fromProjectiveState z) 0 (τ (fromProjectiveState z)))) := by
    filter_upwards [heq] with z hz
    simp only [entranceReturnState, hz]
  have hcState : ContDiffAt ℝ 2 entranceReturnState y :=
    (ContDiffAt.comp (g := fun z => toProjectiveState (normalizedMaxCurve z 0 (τ z)))
      (f := fromProjectiveState) y hcP hcI).congr_of_eventuallyEq heqP
  have hdI := (hcI.differentiableAt (by norm_num)).hasFDerivAt
  have hdTime := (hdτ.comp y hdI).congr_of_eventuallyEq heq
  have hdState := (hdP.comp y hdI).congr_of_eventuallyEq heqP
  refine ⟨hnearValid.self_of_nhds, hcTime, hcState, ?_, ?_, hnearValid⟩
  · simpa only [hT₀] using hdTime
  · simpa only [hT₀] using hdState
