-- Prove2me | solution 1 for BianchiIX.exists_terminal_coreTail_valid
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:06:07.957994+00:00
-- url     : https://prove2.me/submissions/5874f37e-bc16-4d31-a38b-ddc4638590d1

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_exists_normalized_exit_arrival
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_exit_first_hit
import Theorems.Thm_BianchiIX_projectiveDenom_eq
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.toExitTailState_fromExitTailState {v : ℝ} {Y : ExitTailState}
    (hR : 0 < Y 0) (hv : v ^ 2 ≤ (Y 0) ^ 2) :
    toExitTailState (fromExitTailState v Y) = Y := by
  have hs := exitTailGap_sq hv
  have he : coreEnergy (1 - exitTailGap (Y 0) v) v = (Y 0) ^ 2 := by
    dsimp only [coreEnergy]
    nlinarith only [hs]
  ext i
  fin_cases i
  · change Real.sqrt (coreEnergy (1 - exitTailGap (Y 0) v) v) = Y 0
    rw [he, Real.sqrt_sq hR.le]
  · rfl
  · rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_phase_bounds {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : -5 ≤ y 0 ∧ y 0 < 0 := by
  have hR0 : 0 ≤ coreRadius (y 0) (y 2) := Real.sqrt_nonneg _
  have he := coreRadius_sq (y 0) (y 2)
  dsimp only [coreEnergy] at he
  have hR2 := (sq_le_sq₀ hR0 (by norm_num : (0 : ℝ) ≤ 17 / 4)).mpr hy.2.1.2
  have hv0 : 0 ≤ y 2 := (hh.trans_le hy.2.2.2.1.1).le
  constructor
  · nlinarith only [he, hR2, sq_nonneg (y 2)]
  · by_contra hn
    have hm0 : y 0 = 0 := le_antisymm hy.1 (le_of_not_gt hn)
    nlinarith only [he, hm0, hv0, hy.2.2.2.1.2, hy.2.1.1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_denom {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 0 < projectiveStateDenom y ∧ projectiveStateDenom y ≤ 48 := by
  have hm := exitPhysicalRegion_phase_bounds hh hy
  have hm2 : (y 0) ^ 2 ≤ 25 := by nlinarith only [hm.1, hm.2]
  have hu := abs_le.mp hy.2.2.1
  have hw := abs_le.mp hy.2.2.2.2
  have hv : 0 ≤ y 2 ∧ y 2 ≤ 1 := ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩
  have hu2 : (y 1) ^ 2 ≤ 1 := by nlinarith only [hu.1, hu.2]
  have hvw : |y 2 - y 3| ≤ 2 := by
    have H := abs_sub (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hvw2 : (y 2 - y 3) ^ 2 ≤ 4 := by nlinarith only [hvw, abs_nonneg (y 2 - y 3), sq_abs (y 2 - y 3)]
  have hsum : |y 2 + y 3| ≤ 2 := by
    have H := abs_add_le (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hc : |2 * y 1 * (y 2 + y 3)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := mul_le_mul hy.2.2.1 hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    nlinarith only [H]
  change 0 < projectiveDenom (y 0) (y 1) (y 2) (y 3) ∧ projectiveDenom (y 0) (y 1) (y 2) (y 3) ≤ 48
  rw [projectiveDenom_eq]
  constructor
  · nlinarith only [(abs_le.mp hc).2, sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2 - y 3)]
  · nlinarith only [(abs_le.mp hc).1, hm2, hu2, hvw2]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_exit_chart_lower {x : NormalizedState} {h : ℝ} (hh : 0 < h)
    (hA : 1 + x 0 ≠ 0) (hx : stateConstraint x = 1)
    (hy : exitPhysicalRegion h (toProjectiveState x)) : 1 / 8 ≤ 1 + x 0 := by
  have hD := exitPhysicalRegion_denom hh hy
  have H := projective_inverse_scale hA hx
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at H
  rw [← H]
  exact (le_div_iff₀ hD.1).mpr (by linarith only [hD.2])

end
end

private theorem BianchiIX.coreTailEntry_terminal_region {α u w h : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) (hh : h ≤ 1) :
    exitPhysicalRegion h (coreTailEntry ![2 + 2 * α, u, w]) ∧
      coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 = 2 + 2 * α := by
  let Y : ExitTailState := ![2 + 2 * α, u, w]
  have hR : 0 < Y 0 := by change 0 < 2 + 2 * α; linarith only [hα.1]
  have hv : (1 : ℝ) ^ 2 ≤ (Y 0) ^ 2 := by change 1 ^ 2 ≤ (2 + 2 * α) ^ 2; nlinarith only [hα.1]
  have heq : coreTailEntry Y = fromExitTailState 1 Y := by
    ext i
    fin_cases i <;> simp [coreTailEntry, fromExitTailState, exitTailGap]
  have hr := congrFun (toExitTailState_fromExitTailState hR hv) 0
  change coreRadius (fromExitTailState 1 Y 0) 1 = Y 0 at hr
  rw [← heq] at hr
  change coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 = 2 + 2 * α at hr
  refine ⟨⟨?_, ?_, hu, ⟨hh, le_rfl⟩, hw⟩, hr⟩
  · have H := (exitTailGap_compact (R := 2 + 2 * α) (by linarith only [hα.1]) (v := 1) (by norm_num)).1
    change 1 - Real.sqrt ((2 + 2 * α) ^ 2 - 1) ≤ 0
    simpa only [exitTailGap, one_pow, sub_nonpos] using H
  · change 7 / 4 ≤ coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 ∧
      coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 ≤ 17 / 4
    rw [hr]
    constructor <;> linarith only [hα.1, hα.2]


/-- The canonical tail map exists at the D.1 height, uniformly in alpha and in signed wall ratios. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := fromProjectiveState (coreTailEntry Y)
      let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
      coreTailValid h Y ∧ 0 < coreTailTime h Y ∧ coreTailTime h Y ≤ 16 * exitTailLength η α J ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y),
          1 / 8 ≤ 1 + normalizedMaxCurve x 0 t 0 ∧
          exitPhysicalRegion h (β t) ∧
          |β t 1| + |β t 3| ≤ A * b / 2 ∧
          |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| ≤ 40 * A * b ∧
          2 + α < coreRadius (β t 0) (β t 2) ∧ |β t 1| ≤ β t 2 / 2) := by
  obtain ⟨A, hA, ε₀, hε₀, HE⟩ := exists_normalized_exit_arrival hη hJ
  let ε := min ε₀ (1 / 1000)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  refine ⟨A, hA, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hwalls Y h x β
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hh1 : h ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.1.le
    dsimp only [h]
    nlinarith only [H, hη.2]
  have hbε : b ≤ ε := hsmall.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hε.le)
  have hbs : b ≤ 1 / 1000 := hbε.trans (min_le_right _ _)
  have hu : |u| ≤ 1 / 100 := by linarith only [hwalls, hbs, abs_nonneg w]
  have hw : |w| ≤ 1 / 100 := by linarith only [hwalls, hbs, abs_nonneg u]
  obtain ⟨hentry, hRentry⟩ := coreTailEntry_terminal_region hα hu hw hh1
  change exitPhysicalRegion h (coreTailEntry Y) at hentry
  have hD := (exitPhysicalRegion_denom hh hentry).1
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = coreTailEntry Y := by
    dsimp only [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA0 : 0 < 1 + normalizedMaxCurve x 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hV0 : β 0 2 = 1 := by rw [hβ0]; rfl
  have hM0 : β 0 0 < 0 := by rw [hβ0]; exact (exitPhysicalRegion_phase_bounds hh hentry).2
  have hR0 : coreRadius (β 0 0) (β 0 2) = 2 + 2 * α := by rw [hβ0]; exact hRentry
  have hw0 : |β 0 1| + |β 0 3| ≤ b := by rw [hβ0]; exact hwalls
  obtain ⟨T, hT, hhit, hreg, htime, H⟩ := HE x 0 0 α b hc le_rfl hα hb
    (hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))) hA0 hM0 hV0 hR0 hw0
  have hAf (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_of_lt_of_le (by norm_num) (hreg t ht).1
  have HF := normalized_exit_first_hit hc hh le_rfl hT hAf (fun t ht => (hreg t ht).2) hhit
  have hcanonical : coreTailTime h Y = T := HF.1.csInf_eq
  have hvalid : coreTailValid h Y := by
    dsimp only [coreTailValid]
    rw [hcanonical]
    refine ⟨HF.1, ?_, HF.2.2.1, HF.2.2.2, ?_⟩
    · intro t ht
      exact ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1, hAf t ht⟩
    · intro t ht
      exact lt_of_le_of_lt (hreg t ht).2.2.2.2.2 (by norm_num)
  refine ⟨hvalid, by rwa [hcanonical], ?_, ?_⟩
  · rw [hcanonical]
    simpa only [sub_zero] using htime
  · intro t ht
    rw [hcanonical] at ht
    have HB := H t ht
    have HA := normalized_exit_chart_lower hh (ne_of_gt (hAf t ht))
      (normalizedMaxCurve_forward_of_constraint hc ht.1).2.1 (hreg t ht).2
    refine ⟨HA, (hreg t ht).2, HB.1, ?_, HB.2.2⟩
    have HR := HB.2.1
    change |coreRadius (β t 0) (β t 2) - coreRadius (β 0 0) (β 0 2)| ≤ 40 * A * b at HR
    rwa [hR0] at HR
