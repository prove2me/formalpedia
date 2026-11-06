-- Prove2me | solution 1 for BianchiIX.exists_era_survivor_unbounded_orbit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:42:07.050322+00:00
-- url     : https://prove2.me/submissions/10d924e2-c69a-45b2-b32b-a2fc5509697b

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_eraAmplitude_succ
import Theorems.Thm_BianchiIX_eraAmplitude_zero
import Theorems.Thm_BianchiIX_exists_era_input_orbit
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_positive
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
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
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_wall_product (x : NormalizedState) :
    axisCycle x 2 * axisCycle x 3 * axisCycle x 4 = x 2 * x 3 * x 4 := by
  dsimp [axisCycle]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_wall_product (x : NormalizedState) :
    axisSwap x 2 * axisSwap x 3 * axisSwap x 4 = x 2 * x 3 * x 4 := by
  dsimp [axisSwap]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_shears (x : NormalizedState) :
    normalizedShears (axisCycle x) = ![normalizedShears x 1, normalizedShears x 2, normalizedShears x 0] := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_shears (x : NormalizedState) :
    normalizedShears (axisSwap x) = ![normalizedShears x 0, normalizedShears x 2, normalizedShears x 1] := by
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisSwap] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisOrder_bijective : ∀ i, Function.Bijective (axisOrder i) := by decide

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_apply (i : Fin 6) (x : NormalizedState) :
    (axisFrame i).map x =
      ![x, axisCycle x, axisCycle (axisCycle x), axisSwap x,
        axisSwap (axisCycle x), axisSwap (axisCycle (axisCycle x))] i := by
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_walls (i : Fin 6) (x : NormalizedState) :
    normalizedWalls ((axisFrame i).map x) = fun j => normalizedWalls x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_shears (i : Fin 6) (x : NormalizedState) :
    normalizedShears ((axisFrame i).map x) = fun j => normalizedShears x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i
  · ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle x) = _
    rw [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle (axisCycle x)) = _
    simp only [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap x) = _
    rw [axisSwap_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle x)) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle (axisCycle x))) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedState_ext_shears_walls {x y : NormalizedState}
    (hs : normalizedShears x = normalizedShears y) (hw : normalizedWalls x = normalizedWalls y) : x = y := by
  have h₀ := congrFun hs 0
  have h₁ := congrFun hs 1
  change -2 * x 0 = -2 * y 0 at h₀
  change x 0 - Real.sqrt 3 * x 1 = y 0 - Real.sqrt 3 * y 1 at h₁
  have hx₀ : x 0 = y 0 := by linarith
  have hx₁ : x 1 = y 1 := mul_left_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    (by linarith : Real.sqrt 3 * x 1 = Real.sqrt 3 * y 1)
  ext i
  fin_cases i
  · exact hx₀
  · exact hx₁
  · exact congrFun hw 0
  · exact congrFun hw 1
  · exact congrFun hw 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_comp (i j : Fin 6) :
    ∃ k : Fin 6, ∀ x : NormalizedState,
      (axisFrame i).map ((axisFrame j).map x) = (axisFrame k).map x := by
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder i) (axisOrder_bijective i)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder j) (axisOrder_bijective j)
  obtain ⟨k, hk⟩ := axisOrder_covers (σ.trans τ)
  refine ⟨k, fun x => normalizedState_ext_shears_walls ?_ ?_⟩
  · ext l
    simp only [axisFrame_shears, hk]
    rfl
  · ext l
    simp only [axisFrame_walls, hk]
    rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRadiusReturnValid_denom_pos {Y : CoreAngleState} (H : coreRadiusReturnValid Y) :
    0 < projectiveStateDenom (coreRadiusEntry Y) := by
  have hzero := (H.2.1 0 ⟨le_rfl, H.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry Y) - 1) at hzero
  by_contra! hn
  have HD := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, HD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedWallProduct_axisFrame (i : Fin 6) (x : NormalizedState) :
    normalizedWallProduct ((axisFrame i).map x) = normalizedWallProduct x := by
  fin_cases i <;> simp [axisFrame_apply, normalizedWallProduct, axisCycle_wall_product, axisSwap_wall_product]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedWallProduct_coreRadiusEntry_bound {Y : CoreAngleState} {B : ℝ}
    (hu : 0 ≤ Y 1) (hw : 0 ≤ Y 2) (hsum : Y 1 + Y 2 ≤ B) (hB : B ≤ 1 / 4) :
    0 ≤ normalizedWallProduct (fromProjectiveState (coreRadiusEntry Y)) ∧
      normalizedWallProduct (fromProjectiveState (coreRadiusEntry Y)) ≤ B ^ 2 := by
  let y := coreRadiusEntry Y
  have hdenom : projectiveStateDenom y = 4 + (y 0) ^ 2 + (Y 1 - Y 2) ^ 2 - 2 * (Y 1 + Y 2) := by
    dsimp [y, coreRadiusEntry, projectiveStateDenom, projectiveDenom, curvature]
    ring
  have hm : 1 ≤ y 0 := by
    change 1 ≤ 1 + Real.sqrt (Y 0 ^ 2 - 1)
    linarith only [Real.sqrt_nonneg (Y 0 ^ 2 - 1)]
  have hD : 4 ≤ projectiveStateDenom y := by
    rw [hdenom]
    nlinarith only [hsum, hB, hm, sq_nonneg (Y 1 - Y 2)]
  have hDpos : 0 < projectiveStateDenom y := lt_of_lt_of_le (by norm_num) hD
  have hr : (3 / 2 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hrpos : 0 < Real.sqrt 3 := lt_of_lt_of_le (by norm_num) hr
  let a := (6 / projectiveStateDenom y) / Real.sqrt 3
  have ha : 0 ≤ a := (div_pos (div_pos (by norm_num) hDpos) hrpos).le
  have ha1 : a ≤ 1 := (div_le_iff₀ hrpos).mpr
    (((div_le_iff₀ hDpos).mpr (by linarith only [hD]) : 6 / projectiveStateDenom y ≤ 3 / 2).trans
      (by simpa only [one_mul] using hr))
  have heq : normalizedWallProduct (fromProjectiveState y) = a ^ 3 * Y 1 * Y 2 := by
    change (6 / projectiveStateDenom y * Y 1 / Real.sqrt 3) *
      (6 / projectiveStateDenom y * 1 / Real.sqrt 3) *
      (6 / projectiveStateDenom y * Y 2 / Real.sqrt 3) = _
    dsimp only [a]
    ring
  have hB0 : 0 ≤ B := (add_nonneg hu hw).trans hsum
  have hUB : Y 1 ≤ B := (le_add_of_nonneg_right hw).trans hsum
  have hWB : Y 2 ≤ B := (le_add_of_nonneg_left hu).trans hsum
  change 0 ≤ normalizedWallProduct (fromProjectiveState y) ∧ _
  rw [heq]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (1 : ℝ) ^ 3 * B * B := by gcongr
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreArrivalTime_tendsto_atTop {x : NormalizedState} {t B : ℕ → ℝ}
    {Y : ℕ → CoreAngleState} {a : ℕ → Fin 6}
    (hp : positiveWalls x) (hc : stateConstraint x = 1)
    (ht : Monotone t) (ht0 : ∀ n, 0 ≤ t n)
    (hB : Tendsto B atTop (𝓝 0))
    (hsmall : ∀ n, 0 ≤ Y n 1 ∧ 0 ≤ Y n 2 ∧ Y n 1 + Y n 2 ≤ B n ∧ B n ≤ 1 / 4)
    (hactual : ∀ n, fromProjectiveState (coreRadiusEntry (Y n)) =
      (axisFrame (a n)).map (normalizedMaxCurve x 0 (t n))) : Tendsto t atTop atTop := by
  have hbounds (n : ℕ) : 0 ≤ normalizedWallProduct (normalizedMaxCurve x 0 (t n)) ∧
      normalizedWallProduct (normalizedMaxCurve x 0 (t n)) ≤ (B n) ^ 2 := by
    obtain ⟨hu, hw, hs, hcap⟩ := hsmall n
    have H := normalizedWallProduct_coreRadiusEntry_bound hu hw hs hcap
    rw [hactual n, normalizedWallProduct_axisFrame] at H
    exact H
  have hzero : Tendsto (fun n => normalizedWallProduct (normalizedMaxCurve x 0 (t n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hbounds n).1) (fun n => (hbounds n).2)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hB.pow 2
  rcases tendsto_atTop_of_monotone ht with htop | ⟨T, hT⟩
  · exact htop
  · have hT0 : 0 ≤ T := ge_of_tendsto hT (Filter.Eventually.of_forall ht0)
    have hflow := (normalizedMaxCurve_forward hp hc hT0).1.continuousAt.tendsto.comp hT
    have hprod : Tendsto (fun n => normalizedWallProduct (normalizedMaxCurve x 0 (t n))) atTop
        (𝓝 (normalizedWallProduct (normalizedMaxCurve x 0 T))) := by
      have hcont : Continuous normalizedWallProduct := by unfold normalizedWallProduct; fun_prop
      exact hcont.continuousAt.tendsto.comp hflow
    have hpositive := (normalizedMaxCurve_forward hp hc hT0).2.1
    have hprodpos : 0 < normalizedWallProduct (normalizedMaxCurve x 0 T) :=
      mul_pos (mul_pos hpositive.1 hpositive.2.1) hpositive.2.2
    exact False.elim (ne_of_gt hprodpos (tendsto_nhds_unique hprod hzero))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraInputSelection_disjoint {σ Bstar : ℝ} {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (eraInputSelection σ Bstar m) (eraInputSelection σ Bstar n) := by
  apply disjoint_left.mpr
  intro p hm hn
  have hβ : 0 < p.1 ^ σ := Real.rpow_pos_of_pos hm.1.1 _
  have hrm := hm.2.2.2.2.2
  have hrn := hn.2.2.2.2.2
  rcases lt_or_gt_of_ne hmn with h | h
  · have hcast : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith [hrm.2, hrn.1]
  · have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith [hrn.2, hrm.1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraSelectedInputs_disjoint (η : ℝ) (J : ℕ) (σ Bstar : ℝ) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (eraSelectedInputs η J σ Bstar m) (eraSelectedInputs η J σ Bstar n) :=
  (eraInputSelection_disjoint hmn).mono (fun _ h => h.1) (fun _ h => h.1)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraPrefixState_append (η : ℝ) (J : ℕ) (v w : List ℕ+) (p : ℝ × CoreAngleState) :
    eraPrefixState η J (v ++ w) p = eraPrefixState η J w (eraPrefixState η J v p) := by
  induction v generalizing p with
  | nil => rfl
  | cons a v ih => exact ih _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mem_eraPrefixDomain_append (η : ℝ) (J : ℕ) (σ Bstar : ℝ)
    (v w : List ℕ+) (p : ℝ × CoreAngleState) :
    p ∈ eraPrefixDomain η J σ Bstar (v ++ w) ↔
      p ∈ eraPrefixDomain η J σ Bstar v ∧ eraPrefixState η J v p ∈ eraPrefixDomain η J σ Bstar w := by
  induction v generalizing p with
  | nil => simp [eraPrefixDomain, eraPrefixState]
  | cons a v ih =>
    simp only [List.cons_append, eraPrefixDomain, mem_inter_iff, mem_preimage, eraPrefixState,
      Function.comp_apply, ih]
    exact and_assoc.symm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraPrefixState_budget (η : ℝ) (J : ℕ) (w : List ℕ+) (p : ℝ × CoreAngleState)
    (hp : 0 ≤ p.1) : (eraPrefixState η J w p).1 = eraAmplitude p.1 w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [eraPrefixState]
  | append_singleton w a ih =>
    rw [eraPrefixState_append]
    change (eraPrefixState η J w p).1 ^ (4 / 3 : ℝ) = _
    rw [ih, List.length_append, List.length_singleton, eraAmplitude_succ hp]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraPrefixDomain_unique (η : ℝ) (J : ℕ) (σ Bstar : ℝ) {v w : List ℕ+}
    (hlen : v.length = w.length) {p : ℝ × CoreAngleState}
    (hv : p ∈ eraPrefixDomain η J σ Bstar v) (hw : p ∈ eraPrefixDomain η J σ Bstar w) : v = w := by
  induction v generalizing w p with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a v ih =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      have hab : a = b := by
        by_contra hne
        have hd := eraSelectedInputs_disjoint η J σ Bstar
          (fun he => hne (PNat.natPred_injective he))
        exact Set.disjoint_left.mp hd hv.1 hw.1
      subst b
      exact congrArg (List.cons a) (ih (Nat.succ.inj hlen) hv.2 hw.2)

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.exists_next_digit (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    ∃ a : ℕ+, word p (n + 1) = word p n ++ [a] := by
  have hl := word_length p (n + 1)
  have hp := mem_word_domain p (n + 1)
  generalize word p (n + 1) = w at hl hp ⊢
  induction w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton w a _ =>
    have hw : w = word p n := eraPrefixDomain_unique η J σ Bstar
      (by simpa [word_length] using hl)
      ((mem_eraPrefixDomain_append η J σ Bstar w [a] p.val).mp hp).1 (mem_word_domain p n)
    exact ⟨a, congrArg (fun v => v ++ [a]) hw⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.word_succ (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    word p (n + 1) = word p n ++ [digits p n] := (exists_next_digit p n).choose_spec

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

attribute [local instance] BianchiIX.instMeasurableSpaceListPNat_bianchiIX
private theorem BianchiIX.EraSurvivor.budgetState_zero (p : eraSurvivorDomain η J σ Bcap) : budgetState p 0 = p.val := by
  have hw : word p 0 = [] := List.length_eq_zero_iff.mp (word_length p 0)
  simp only [budgetState, hw, eraPrefixState, id_eq]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

attribute [local instance] BianchiIX.instMeasurableSpaceListPNat_bianchiIX
private theorem BianchiIX.EraSurvivor.budgetState_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    budgetState p (n + 1) = eraBudgetReturn η J (digits p n).natPred (budgetState p n) := by
  unfold budgetState
  rw [word_succ, eraPrefixState_append]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

attribute [local instance] BianchiIX.instMeasurableSpaceListPNat_bianchiIX
private theorem BianchiIX.EraSurvivor.budgetState_mem_selected (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    budgetState p n ∈ eraSelectedInputs η J σ Bcap (digits p n).natPred := by
  have H := mem_word_domain p (n + 1)
  rw [word_succ] at H
  exact ((mem_eraPrefixDomain_append η J σ Bcap (word p n) [digits p n] p.val).mp H).2.1

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.elapsedTime_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    elapsedTime p (n + 1) = duration p n + elapsedTime p n := by
  rw [elapsedTime, Finset.sum_range_succ]
  exact add_comm _ _

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.frame_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) (x : NormalizedState) :
    (axisFrame (frame p (n + 1))).map x =
      (axisFrame (eraReturnFrame (digits p n).natPred)).map ((axisFrame (frame p n)).map x) :=
  ((axisFrame_comp (eraReturnFrame (digits p n).natPred) (frame p n)).choose_spec x).symm

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.state_zero (p : eraSurvivorDomain η J σ Bcap) : state p 0 = p.val.2 :=
  congrArg Prod.snd (budgetState_zero p)

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.state_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    state p (n + 1) = eraNextState η J (digits p n).natPred (state p n) :=
  congrArg Prod.snd (budgetState_succ p n)

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.budgetState_budget (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    (budgetState p n).1 = eraAmplitude p.val.1 n := by
  have hp : 0 < p.val.1 := by
    have H := (budgetState_mem_selected p 0).1.1.1
    rwa [budgetState_zero] at H
  rw [budgetState, eraPrefixState_budget η J (word p n) p.val hp.le, word_length]

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.physical_orbit (p : eraSurvivorDomain η J σ Bcap)
    (H : ∀ n, 0 < duration p n ∧ coreRadiusReturnValid (state p n) ∧
      fromProjectiveState (coreRadiusEntry (state p (n + 1))) =
        (axisFrame (eraReturnFrame (digits p n).natPred)).map
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry (state p n))) 0 (duration p n))) :
    StrictMono (elapsedTime p) ∧ ∀ n,
      elapsedTime p n ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.val.2)) 0 ∧
      fromProjectiveState (coreRadiusEntry (state p n)) = (axisFrame (frame p n)).map
        (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (elapsedTime p n)) := by
  let x := fromProjectiveState (coreRadiusEntry p.val.2)
  have hpos (n : ℕ) : 0 < duration p n := (H n).1
  have hnonneg (n : ℕ) : 0 ≤ elapsedTime p n :=
    Finset.sum_nonneg (fun j _ => (hpos j).le)
  have hc : stateConstraint x = 1 := by
    have HV := (H 0).2.1
    rw [state_zero] at HV
    exact fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos HV).ne'
  have hdom (n : ℕ) : elapsedTime p n ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 (hnonneg n)
  refine ⟨strictMono_nat_of_lt_succ (fun n => by rw [elapsedTime_succ]; linarith only [hpos n]), ?_⟩
  intro n
  refine ⟨hdom n, ?_⟩
  induction n with
  | zero =>
    simp only [state_zero, elapsedTime, Finset.range_zero, Finset.sum_empty, normalizedMaxCurve_initial]
    rfl
  | succ n ih =>
    have hcT := (normalizedMaxCurve_forward_of_constraint hc (hnonneg n)).2.1
    have hs := normalizedMaxCurve_shift (t₀ := (0 : ℝ)) (t := duration p n)
      (by simpa only [zero_add] using hdom n)
      (by simpa only [elapsedTime_succ] using hdom (n + 1))
    simp only [zero_add] at hs
    rw [(H n).2.2, ih, (axisFrame (frame p n)).maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hcT 0 (hpos n).le),
      hs, elapsedTime_succ, frame_succ]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_era_survivor_orbit :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ p : eraSurvivorDomain η J σ Bcap,
            (∀ n, 0 < EraSurvivor.duration p n ∧ coreRadiusReturnValid (EraSurvivor.state p n) ∧
              Nat.floor (EraSurvivor.state p n 0 / 2) = (EraSurvivor.digits p n : ℕ)) ∧
            StrictMono (EraSurvivor.elapsedTime p) ∧ ∀ n,
              EraSurvivor.elapsedTime p n ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.val.2)) 0 ∧
              fromProjectiveState (coreRadiusEntry (EraSurvivor.state p n)) =
                (axisFrame (EraSurvivor.frame p n)).map (normalizedMaxCurve
                  (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (EraSurvivor.elapsedTime p n)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_input_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hB, hBone, HB⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bstar, hB, hBone, ?_⟩
  intro Bcap hcap p
  have Hinput (n : ℕ) : EraSurvivor.budgetState p n ∈
      eraInputSelection σ Bstar (EraSurvivor.digits p n).natPred := by
    have H := (EraSurvivor.budgetState_mem_selected p n).1
    exact ⟨⟨H.1.1, H.1.2.trans hcap⟩, H.2⟩
  have Hstep (n : ℕ) := HB (EraSurvivor.digits p n).natPred (EraSurvivor.budgetState p n) (Hinput n)
  refine ⟨fun n => ⟨(Hstep n).1, (Hstep n).2.2.2.1, ?_⟩, ?_⟩
  · simpa only [EraSurvivor.state, PNat.natPred_add_one] using (Hstep n).2.2.2.2
  · apply EraSurvivor.physical_orbit p
    intro n
    refine ⟨(Hstep n).1, (Hstep n).2.2.2.1, ?_⟩
    rw [EraSurvivor.state_succ]
    exact (Hstep n).2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.budgetState_tendsto_zero (p : eraSurvivorDomain η J σ Bcap) (hcap : Bcap < 1) :
    Tendsto (fun n => (budgetState p n).1) atTop (𝓝 0) := by
  have hp := (budgetState_mem_selected p 0).1.1
  rw [budgetState_zero] at hp
  simp_rw [budgetState_budget, eraAmplitude]
  exact (tendsto_rpow_atTop_of_base_lt_one p.val.1 (by linarith only [hp.1])
    (hp.2.trans_lt hcap)).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4 / 3))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.elapsedTime_tendsto_atTop (p : eraSurvivorDomain η J σ Bcap) (hcap : Bcap ≤ 1 / 4)
    (hvalid : coreRadiusReturnValid p.val.2) (ht : StrictMono (elapsedTime p))
    (hactual : ∀ n, fromProjectiveState (coreRadiusEntry (state p n)) =
      (axisFrame (frame p n)).map
        (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (elapsedTime p n))) :
    Tendsto (elapsedTime p) atTop atTop := by
  have hinput (n : ℕ) := (budgetState_mem_selected p n).1
  have hinit := hinput 0
  rw [budgetState_zero] at hinit
  have hD := coreRadiusReturnValid_denom_pos hvalid
  have hp : positiveWalls (fromProjectiveState (coreRadiusEntry p.val.2)) :=
    fromProjectiveState_positive hD ⟨hinit.2.2.1, by change (0 : ℝ) < 1; norm_num, hinit.2.2.2.1⟩
  apply coreArrivalTime_tendsto_atTop hp (fromProjectiveState_constraint hD.ne') ht.monotone
    (fun n => by simpa only [elapsedTime, Finset.range_zero, Finset.sum_empty] using ht.monotone (Nat.zero_le n))
    (budgetState_tendsto_zero p (hcap.trans_lt (by norm_num))) _ hactual
  intro n
  exact ⟨(hinput n).2.2.1.le, (hinput n).2.2.2.1.le, (hinput n).2.2.2.2.1,
    (hinput n).1.2.trans hcap⟩

end
end

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology



/-- All retained infinite histories are actual unbounded-time trajectories, with each selected digit identified by its entry radius. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ p : eraSurvivorDomain η J σ Bcap,
            (∀ n, 0 < EraSurvivor.duration p n ∧ coreRadiusReturnValid (EraSurvivor.state p n) ∧
              Nat.floor (EraSurvivor.state p n 0 / 2) = (EraSurvivor.digits p n : ℕ)) ∧
            StrictMono (EraSurvivor.elapsedTime p) ∧
            Tendsto (EraSurvivor.elapsedTime p) atTop atTop ∧ ∀ n,
              EraSurvivor.elapsedTime p n ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.val.2)) 0 ∧
              fromProjectiveState (coreRadiusEntry (EraSurvivor.state p n)) =
                (axisFrame (EraSurvivor.frame p n)).map (normalizedMaxCurve
                  (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (EraSurvivor.elapsedTime p n)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_survivor_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hB, hBone, HB⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨min Bstar (1 / 4), lt_min hB (by norm_num), (min_le_left _ _).trans_lt hBone, ?_⟩
  intro Bcap hcap p
  obtain ⟨Hstep, Hmono, Horbit⟩ := HB Bcap (hcap.trans (min_le_left _ _)) p
  have hvalid : coreRadiusReturnValid p.val.2 := by
    simpa only [EraSurvivor.state_zero] using (Hstep 0).2.1
  exact ⟨Hstep, Hmono, EraSurvivor.elapsedTime_tendsto_atTop p
    (hcap.trans (min_le_right _ _)) hvalid Hmono (fun n => (Horbit n).2), Horbit⟩
