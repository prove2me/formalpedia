-- Prove2me | solution 1 for BianchiIX.exists_era_event_itinerary
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:35:22.692418+00:00
-- url     : https://prove2.me/submissions/84dfbba1-c920-4b7a-84ca-4c012da31489

import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_coreRadiusReturn_exit_chart
import Theorems.Thm_BianchiIX_exists_core_itinerary
import Theorems.Thm_BianchiIX_exists_era_bounded_phase_estimates
import Theorems.Thm_BianchiIX_exists_reflectionReturn_phase_bounds
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Theorems.Thm_BianchiIX_projectiveDenom_eq
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

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_constraint (x : NormalizedState) : stateConstraint (axisSwap x) = stateConstraint x := by
  dsimp [stateConstraint, constraint, shearSq, curvature, axisSwap]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toProjectiveState_axisSwap (x : NormalizedState) :
    toProjectiveState (axisSwap x) = projectiveReflection (toProjectiveState x) := by
  ext i
  fin_cases i <;> dsimp [toProjectiveState, axisSwap, projectiveReflection, projectiveCoord]
  all_goals ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.unit_active_wall_denom_pos {y : ProjectiveState} (hv : y 2 = 1)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 4) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 4) :
    0 < projectiveStateDenom y := by
  have hp : y 1 * (1 + y 3) ≤ 5 / 16 := by
    have H := mul_le_mul hu.2 (by linarith only [hw.2] : 1 + y 3 ≤ 5 / 4)
      (by linarith only [hw.1] : 0 ≤ 1 + y 3) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    norm_num at H
    exact H
  rw [projectiveStateDenom, projectiveDenom_eq, hv]
  nlinarith only [hp, sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (1 - y 3)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRadiusEntry_upward {Y : CoreAngleState} (hk : 2 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 4) (hw : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 4) :
    projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) = 1 ∧
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) 0 0 := by
  have hD := unit_active_wall_denom_pos (y := coreRadiusEntry Y) rfl hu hw
  have hc := fromProjectiveState_constraint hD.ne'
  have hA := fromProjectiveState_clock_pos hD
  have hcoords := toProjectiveState_fromProjectiveState hD.ne'
  have hroot : 1 ≤ Real.sqrt (Y 0 ^ 2 - 1) := by
    exact (Real.le_sqrt (by norm_num) (by nlinarith only [hk])).mpr (by nlinarith only [hk])
  have hprod : Y 1 * (1 + Y 2) ≤ 5 / 16 := by
    have H := mul_le_mul hu.2 (by linarith only [hw.2] : 1 + Y 2 ≤ 5 / 4)
      (by linarith only [hw.1] : 0 ≤ 1 + Y 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    norm_num at H
    exact H
  constructor
  · exact congrFun hcoords 2
  · rw [normalizedEventRate, normalizedMaxCurve_initial, projectiveActiveWall_fderiv_field hA.ne' hc,
      hcoords]
    apply mul_pos hA
    change 0 < activeVelocity (1 + Real.sqrt (Y 0 ^ 2 - 1)) (Y 1) 1 (Y 2)
    dsimp only [activeVelocity, coupling]
    nlinarith only [hroot, hprod, sq_nonneg (Y 1)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.reflectionReturn_first_active {Z : CoreAngleState}
    (hD : 0 < projectiveStateDenom (coreTailEntry Z))
    (hfirst : IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Z) 0 t 3 = 1}
      (reflectionReturnTime Z))
    (hactual : coreRadiusEntry (reflectionReturnState Z) =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry Z) 0 (reflectionReturnTime Z))) :
    let x := axisSwap (fromProjectiveState (coreTailEntry Z))
    IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} (reflectionReturnTime Z) ∧
      toProjectiveState (normalizedMaxCurve x 0 (reflectionReturnTime Z)) =
        coreRadiusEntry (reflectionReturnState Z) := by
  intro x
  have hc := fromProjectiveState_constraint hD.ne'
  have hcx : stateConstraint x = 1 := (axisSwap_constraint _).trans hc
  have hdom (t : ℝ) (ht : 0 ≤ t) := normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht
  have hflow (t : ℝ) (ht : 0 ≤ t) :
      toProjectiveState (normalizedMaxCurve x 0 t) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Z) 0 t) := by
    have hs := NormalizedSymmetry.swap.maxCurve (hdom t ht)
    change normalizedMaxCurve x 0 t =
      axisSwap (normalizedMaxCurve (fromProjectiveState (coreTailEntry Z)) 0 t) at hs
    rw [hs, toProjectiveState_axisSwap]
    rfl
  refine ⟨⟨⟨hfirst.1.1, normalizedMaxDomain_contains_Ici_of_constraint hcx 0 hfirst.1.1.le, ?_⟩,
    ?_⟩, (hflow _ hfirst.1.1.le).trans hactual.symm⟩
  · exact (congrFun (hflow _ hfirst.1.1.le) 2).trans hfirst.1.2
  · intro t ht
    apply hfirst.2
    exact ⟨ht.1, (congrFun (hflow t ht.1.le) 2).symm.trans ht.2.2⟩

end
end


/-- The phase-margin estimates certify every event in the block, including first arrivals in the new axis chart. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        X 1 + X 2 ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        C * (X 1 + X 2) < β / 4 → EraEventItinerary η J m X := by
  obtain ⟨δ, hδ, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨εK, hεK, hεKmax, K, hK, HK⟩ := exists_core_itinerary
  obtain ⟨εR, hεR, _, _, _, HR⟩ := exists_reflectionReturn_phase_bounds
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨εP, hεP, _, CP, hCP, Hp⟩ := HP η hη hηδ J hJ
  let ε := min εP (min εK (εR / 4))
  let C := max CP K
  have hε : 0 < ε := lt_min hεP (lt_min hεK (div_pos hεR (by norm_num)))
  have hεP' : ε ≤ εP := min_le_left _ _
  have hεK' : ε ≤ εK := (min_le_right _ _).trans (min_le_left _ _)
  have hεR' : ε ≤ εR / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, C, hCP.trans (le_max_left _ _), ?_⟩
  intro m β X hβ hβmax hu hw hsmall hphase hmargin
  let F := coreReturnState coreRadiusReturnTime
  let G := coreReflectionState coreRadiusReturnTime
  let b := X 1 + X 2
  have hb : 0 < b := add_pos hu.1 hw.1
  have hX : 2 < X 0 := by nlinarith only [hphase.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hX0 : 0 < X 0 := lt_trans (by norm_num) hX
  have hscale {e : ℝ} (he : ε ≤ e) : ε / X 0 ≤ e / X 0 :=
    div_le_div_of_nonneg_right he hX0.le
  have hbound {c : ℝ} (hc : c ≤ C) : c * b < β / 4 :=
    (mul_le_mul_of_nonneg_right hc hb.le).trans_lt hmargin
  obtain ⟨Hall, Hconn, Hlast, _, _⟩ := HK m β X hβ hβmax
    ⟨hu.1, hu.2.trans (hscale hεK')⟩ ⟨hw.1, hw.2.trans (hscale hεK')⟩ hphase
    ((hbound (le_max_right _ _)).trans (by linarith only [hβ]))
  obtain ⟨_, _, _, _, _, _, hcount, _, _, _, hterminal, _, Hfirst, Hactual, Hunit, Hup, _⟩ :=
    Hp m β X hβ hβmax ⟨hu.1, hu.2.trans (hscale hεP')⟩ ⟨hw.1, hw.2.trans (hscale hεP')⟩
      (hsmall.trans (mul_le_mul_of_nonneg_right hεP' (pow_nonneg (half_pos hβ).le _)))
      hphase (hbound (le_max_left _ _))
  have hbX : b * X 0 ≤ 2 * ε := by
    dsimp only [b]
    nlinarith only [(le_div_iff₀ hX0).mp hu.2, (le_div_iff₀ hX0).mp hw.2]
  have hbquarter : b ≤ 1 / 4 :=
    (hsmall.trans (mul_le_of_le_one_right hε.le
      (pow_le_one₀ (half_pos hβ).le (by linarith only [hβmax])))).trans
      (hεK'.trans (hεKmax.trans (by norm_num)))
  have Hz (j : ℕ) (hj : j ≤ m) (i : Fin 2) :
      0 < F (G^[j] X) i.succ ∧ F (G^[j] X) i.succ ≤ b := by
    obtain ⟨_, _, _, _, _, Hpos, Hsum, _⟩ := Hall j hj
    refine ⟨Hpos i, ?_⟩
    fin_cases i
    · exact (le_add_of_nonneg_right (Hpos 1).le).trans Hsum
    · exact (le_add_of_nonneg_left (Hpos 0).le).trans Hsum
  have Hreflect (j : ℕ) (hj : j < m) := by
    let Z := F (G^[j] X)
    have hZ4 : 31 / 8 ≤ Z 0 := by linarith only [(Hconn j hj).1, hβ]
    have hZ0 : 0 < Z 0 := lt_of_lt_of_le (by norm_num) hZ4
    have hZupper : Z 0 ≤ 2 * X 0 := by
      have he : |Z 0 - (X 0 - 2 * j)| < β / 4 :=
        ((le_add_of_nonneg_left (abs_nonneg _)).trans (Hall j hj.le).2.2.2.2.2.2.2.1).trans_lt
          (hbound (le_max_right _ _))
      nlinarith only [(abs_lt.mp he).2, hβmax, hX, Nat.cast_nonneg (α := ℝ) j]
    have hsmallZ (i : Fin 2) : 0 < Z i.succ ∧ Z i.succ ≤ εR / Z 0 := by
      refine ⟨(Hz j hj.le i).1, (le_div_iff₀ hZ0).mpr ?_⟩
      calc
        _ ≤ b * Z 0 := mul_le_mul_of_nonneg_right (Hz j hj.le i).2 hZ0.le
        _ ≤ b * (2 * X 0) := mul_le_mul_of_nonneg_left hZupper hb.le
        _ ≤ εR := by nlinarith only [hbX, hεR']
    exact HR Z hZ4 (hsmallZ 0) (hsmallZ 1)
  have Hentry (j : ℕ) (hj : j ≤ m) (i : Fin 2) :
      0 ≤ (G^[j] X) i.succ ∧ (G^[j] X) i.succ ≤ 1 / 4 := by
    cases j with
    | zero =>
      fin_cases i
      · exact ⟨hu.1.le, (le_add_of_nonneg_right hw.1.le).trans hbquarter⟩
      · exact ⟨hw.1.le, (le_add_of_nonneg_left hu.1.le).trans hbquarter⟩
    | succ j =>
      have hjm : j < m := by omega
      have Hwall := (Hreflect j hjm).2.2.2.2.2.1 i
      rw [Function.iterate_succ_apply']
      exact ⟨Hwall.1.le, Hwall.2.trans ((Hz j hjm.le i).2.trans hbquarter)⟩
  refine ⟨?_, ?_, ⟨hterminal, Hfirst, Hactual, Hunit, Hup⟩, hcount⟩
  · intro j hj
    have hk : 2 < G^[j] X 0 := by linarith only [(Hall j hj).1, hβ]
    have hR : 2 ≤ F (G^[j] X) 0 := by
      rcases lt_or_eq_of_le hj with hlt | rfl
      · linarith only [(Hconn j hlt).1, hβ]
      · linarith only [Hlast.1, hβ]
    exact ⟨hk, coreRadiusEntry_upward hk.le (Hentry j hj 0) (Hentry j hj 1),
      (Hall j hj).2.1, coreRadiusReturn_exit_chart (Hall j hj).2.1 hR
        ⟨(Hz j hj 0).1.le, (Hz j hj 0).2.trans hbquarter⟩
        ⟨(Hz j hj 1).1.le, (Hz j hj 1).2.trans hbquarter⟩⟩
  · intro j hj
    obtain ⟨hf, ha, _⟩ := Hreflect j hj
    have hD := unit_active_wall_denom_pos (y := coreTailEntry (F (G^[j] X))) rfl
      ⟨(Hz j hj.le 0).1.le, (Hz j hj.le 0).2.trans hbquarter⟩
      ⟨(Hz j hj.le 1).1.le, (Hz j hj.le 1).2.trans hbquarter⟩
    obtain ⟨hfirst, hactual⟩ := reflectionReturn_first_active hD hf ha
    refine ⟨by linarith only [(Hconn j hj).1, hβ], hfirst, ?_, (Hconn j hj).2.2⟩
    simpa only [Function.iterate_succ_apply', F, G, coreReflectionState,
      coreConnectionParameters, reflectionReturnState] using hactual
