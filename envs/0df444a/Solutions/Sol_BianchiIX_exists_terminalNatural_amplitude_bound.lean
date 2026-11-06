-- Prove2me | solution 1 for BianchiIX.exists_terminalNatural_amplitude_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:31:41.513196+00:00
-- url     : https://prove2.me/submissions/623f5a7a-69b1-455e-a51c-869ebfb8be71

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_decay
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entranceReturn_walls_pos
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_terminalWallFactor_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint_uniform
import Theorems.Thm_BianchiIX_exists_terminal_cycle_entrance_inputs_uniform
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_homogeneous_solution_eq_exp_integral_Icc
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_scaled_entrance_strong_rate_integral
import Theorems.Thm_BianchiIX_terminal_amplitude_power_budget
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
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
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX

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
open Set MeasureTheory

private theorem BianchiIX.scaled_entrance_arc_decay {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    Y t 1 ≤ Y s 1 * Real.exp ((2 * Y s 3 + 3 * (Y s 1) ^ 2) / k) *
      Real.exp (-(1 + 99 * k / 200) * (Real.log (Y t 2) - Real.log (Y s 2))) := by
  let b := fun r => a r * connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3)
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hbc : ContinuousOn b (Icc s t) := by
    apply hac.mul
    unfold connectionStrongRate
    fun_prop
  have heq : Y t 1 = Y s 1 * Real.exp (∫ r in s..t, b r) := by
    apply homogeneous_solution_eq_exp_integral_Icc hst hbc (hcoord 1)
    intro r hr
    convert! hasDerivAt_pi.mp (hY r (Ioo_subset_Icc_self hr)) 1 using 1
    change _ = a r * strongVelocity _ _ _ _
    dsimp [b, connectionStrongRate, strongVelocity]
    ring
  rw [heq]
  have H := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (scaled_entrance_strong_rate_integral hk hst hY hac ha hy hv)) (hy s ⟨le_rfl, hst⟩).2.2.1.1
  apply H.trans_eq
  rw [Real.exp_add]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalized_entrance_arc_decay {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 →
    Y t 1 ≤ Y s 1 * Real.exp ((2 * Y s 3 + 3 * (Y s 1) ^ 2) / k) *
      Real.exp (-(1 + 99 * k / 200) * (Real.log (Y t 2) - Real.log (Y s 2))) := by
  intro Y hy hvs
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y
      (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1) (hA s hsm) (hA r hr) 1 hvs
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  exact scaled_entrance_arc_decay hk hst hY hac (fun r hr => (hA r hr).le) hy hv

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

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entrance_arc_prefactor_bound {k u w : ℝ} (hk : 7 / 4 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    Real.exp ((2 * w + 3 * u ^ 2) / k) ≤ Real.exp (1 / 1000) := by
  have hk0 : 0 < k := by linarith
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hk0).mpr
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  nlinarith only [hw.2, hu2, hk]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_power_decay {y : ProjectiveState}
    (hk : 19 / 10 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ Real.exp (1 / 1000) * (y 1 * (y 2) ^ (19 / 10 : ℝ)) ∧
      entranceReturnState y 3 ≤ y 3 * y 2 := by
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith
  have hD := entrance_initial_denom_pos hk' hm hu hv hw
  have hc := fromProjectiveState_constraint hD.ne'
  have HR := (entranceReturn_regular hk' hm hu hv hw).1
  have ht : 0 ≤ entranceReturnTime y := HR.1.1.1.le
  have hinit : projectiveOriginalFlow y 0 0 = y := projectiveOriginalFlow_initial hD 0
  have H := normalized_entrance_arc_decay hc hk' le_rfl ht
    (fun r hr => (HR.2.1 r hr).2) (entranceReturn_region hk' hm hu hv hw)
    (by change 0 < projectiveOriginalFlow y 0 0 2; rw [hinit]; exact hv.1)
  change entranceReturnState y 1 ≤ projectiveOriginalFlow y 0 0 1 *
    Real.exp ((2 * projectiveOriginalFlow y 0 0 3 + 3 * (projectiveOriginalFlow y 0 0 1) ^ 2) /
      coreRadius (y 0) (y 2)) * Real.exp (-(1 + 99 * coreRadius (y 0) (y 2) / 200) *
        (Real.log (entranceReturnState y 2) - Real.log (projectiveOriginalFlow y 0 0 2))) at H
  rw [hinit, (entranceReturn_active_component hk' hm hu hv hw).1,
    Real.log_one, zero_sub, neg_mul_neg] at H
  have hpow : Real.exp ((1 + 99 * coreRadius (y 0) (y 2) / 200) * Real.log (y 2)) ≤
      (y 2) ^ (19 / 10 : ℝ) := by
    rw [Real.rpow_def_of_pos hv.1]
    apply Real.exp_le_exp.mpr
    have he : 19 / 10 ≤ 1 + 99 * coreRadius (y 0) (y 2) / 200 := by linarith
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr he)
      (Real.log_nonpos hv.1.le hv.2.le)]
  refine ⟨H.trans ?_, ?_⟩
  · calc
      _ ≤ (y 1 * Real.exp (1 / 1000)) * (y 2) ^ (19 / 10 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (entrance_arc_prefactor_bound hk' hu hw) hu.1)
          hpow (Real.exp_pos _).le (mul_nonneg hu.1 (Real.exp_pos _).le)
      _ = _ := by ring
  · exact (entranceReturn_decay hk' hm hu hv hw).2.trans
      (mul_le_of_le_one_right (mul_nonneg hw.1 hv.1.le)
        (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (by simpa using Real.log_nonpos hv.1.le hv.2.le) hk0.le)))

end
end


/-- The actual natural-height terminal output has superlinear amplitude contraction, uniformly in the wall ratio. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 40000)
    {J : ℕ} (hJ : 20 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ α b U W : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      0 < terminalNaturalState η J Y 1 ∧ 0 < terminalNaturalState η J Y 3 ∧
        terminalNaturalState η J Y 1 + terminalNaturalState η J Y 3 ≤ C * b ^ (19 / 10 : ℝ) := by
  have hη100 : 0 < η ∧ η ≤ 1 / 100 := ⟨hη.1, by linarith [hη.2]⟩
  obtain ⟨A, hA, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη100 (by omega : 2 ≤ J)
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform
    (εin := 1 / 10000) (q := 0) (by norm_num) hη100 (by omega : 0 + 2 ≤ J)
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη100 (by omega : 2 ≤ J)
  let ε := min 1 (min εm (min εi εg))
  let C := (Real.exp (1 / 1000) + 1) * A ^ 2
  have hε : 0 < ε := lt_min (by norm_num) (lt_min hεm (lt_min hεi hεg))
  have hA0 : 0 ≤ A := by linarith
  have hC : 1 ≤ C := by
    have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA
    dsimp [C]
    nlinarith only [hA2, mul_nonneg (Real.exp_pos (1 / 1000)).le (sq_nonneg A)]
  refine ⟨C, hC, ε, hε, min_le_left _ _, ?_⟩
  intro α b U W hα hb hsmall hsum hU hW Y
  have hα0 := hα.1
  let h := η * α ^ J
  let z := terminalEntranceInput h Y
  let y := terminalCyclicInput h Y
  have hs {e : ℝ} (he : ε ≤ e) : b ≤ e * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right he (pow_nonneg hα.1.le _))
  obtain ⟨_, Hvfac, Hwfac, Hu, _, Hfactor⟩ := HM η α b U W le_rfl hη100.2 hα hb
    (hs ((min_le_right _ _).trans (min_le_left _ _))) hsum
  obtain ⟨_, _, _, Hm, HU, HV, HW, _, _⟩ := HI η α b U W le_rfl hη100.2
    (by norm_num; exact hη.2) hα hb
    (hs ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hsum hU hW
  have HK := (HG η α b U W le_rfl hη100.2 hα hb
    (hs ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hsum).2.2.2.2.1
  change 19 / (10 * α) < coreRadius (y 0) (y 2) ∧ _ at HK
  have hlow : 19 / 10 ≤ 19 / (10 * α) := (le_div_iff₀ (by positivity)).mpr (by linarith [hα.2])
  have hk : 19 / 10 ≤ coreRadius (y 0) (y 2) := hlow.trans HK.1.le
  change 2 < y 0 at Hm
  change 0 < y 1 ∧ y 1 ≤ 1 / 10000 ∧ _ at HU
  change 0 < y 2 ∧ y 2 < 1 / 2 at HV
  change 0 < y 3 ∧ y 3 ≤ 1 / 10000 ∧ _ at HW
  have hm : 1 ≤ y 0 := by linarith
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨HV.1, by linarith [HV.2]⟩
  have Hdec := entranceReturn_power_decay hk hm ⟨HU.1.le, HU.2.1⟩ hv ⟨HW.1.le, HW.2.1⟩
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith
  have Hvalid := (entranceReturn_regular hk' hm ⟨HU.1.le, HU.2.1⟩ hv ⟨HW.1.le, HW.2.1⟩).1
  have Hpos := entranceReturn_walls_pos hk' hm ⟨HU.1, HU.2.1⟩ hv ⟨HW.1, HW.2.1⟩
    (entranceReturnTime y) ⟨Hvalid.1.1.1.le, le_rfl⟩
  change z 2 = W * terminalWallFactor h Y 1 at Hvfac
  change z 3 = U * terminalWallFactor h Y 0 at Hwfac
  have hvscale : y 2 ≤ A * W / α ^ 2 := by
    change z 2 ≤ _
    rw [Hvfac]
    exact (mul_le_mul_of_nonneg_left (Hfactor 1).2.2.2.1 hW.le).trans_eq (by ring)
  have hwscale : y 3 ≤ A * U / α ^ 2 := by
    change z 3 ≤ _
    rw [Hwfac]
    exact (mul_le_mul_of_nonneg_left (Hfactor 0).2.2.2.1 hU.le).trans_eq (by ring)
  have huscale : y 1 ≤ α ^ (4 : ℕ) := by
    exact (Hu.2.trans (mul_le_of_le_one_left (pow_nonneg hα.1.le _)
      (by linarith [hη.2] : 2 * η ≤ 1))).trans
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 4 ≤ J - 2))
  have hbα : b ≤ α ^ (40 : ℕ) :=
    (hsmall.trans (mul_le_of_le_one_left (pow_nonneg hα.1.le _) (min_le_left _ _))).trans
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 40 ≤ 2 * J))
  have Hp := terminal_amplitude_power_budget hα hb hbα hA hU.le hW.le
    (by simpa only [abs_of_pos hU, abs_of_pos hW] using hsum)
    ⟨HU.1.le, huscale⟩ ⟨hv.1.le, hvscale⟩ ⟨HW.1.le, hwscale⟩
  have hstate : terminalNaturalState η J Y = entranceReturnState y := by
    change terminalConnectionState (η * ((Y 0 - 2) / 2) ^ J) Y = _
    rw [show (Y 0 - 2) / 2 = α by change (2 + 2 * α - 2) / 2 = α; ring]
    rfl
  rw [hstate]
  refine ⟨Hpos.1, Hpos.2.2, ?_⟩
  calc
    _ ≤ Real.exp (1 / 1000) * (A ^ 2 * b ^ (19 / 10 : ℝ)) + A ^ 2 * b ^ (19 / 10 : ℝ) :=
      add_le_add (Hdec.1.trans (mul_le_mul_of_nonneg_left Hp.1 (Real.exp_pos _).le)) (Hdec.2.trans Hp.2)
    _ = _ := by dsimp [C]; ring
