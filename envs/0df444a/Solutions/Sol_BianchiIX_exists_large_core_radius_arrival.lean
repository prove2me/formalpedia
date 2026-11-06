-- Prove2me | solution 1 for BianchiIX.exists_large_core_radius_arrival
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:40:49.673537+00:00
-- url     : https://prove2.me/submissions/270e7742-d944-42a5-bce7-d4d3fa749d2b

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRadiusEntry_variation_bounds
import Theorems.Thm_BianchiIX_core_radius_arrival_error
import Theorems.Thm_BianchiIX_eventually_coreRadius_firstReturn
import Theorems.Thm_BianchiIX_exists_large_core_exit_derivative
import Theorems.Thm_BianchiIX_exists_large_core_radius_variation
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

end
end

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

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreProjectedFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (w : ProjectiveState) :
    coreProjectedFlowVariation y t₀ t₀ w = coreClockProjection y w := by
  rw [coreProjectedFlowVariation, projectiveOriginalFlow_initial hD,
    projectiveFlowDifferential_initial hD, ContinuousLinearMap.id_apply]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_region {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    coreRegion (Y 0) (coreRadiusEntry Y) := by
  have hR := coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)
  have he := coreRadius_sq (coreRadiusEntry Y 0) (coreRadiusEntry Y 2)
  rw [hR] at he
  refine ⟨?_, le_rfl, hu, ?_⟩
  · rw [← he, sub_self, abs_zero]
    norm_num
  · simpa [coreRadiusEntry] using hw

end
end

/-- Formula (B.34) for the actual moving-exit map in incoming radius coordinates. -/
theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      ∃ τ : CoreAngleState → ℝ, τ Y = T ∧ ContDiffAt ℝ 1 τ Y ∧
        (∀ᶠ Z in 𝓝 Y,
          IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
            ∀ t ∈ Icc 0 (τ Z), t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
              0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 t 0) ∧
        let F := fun Z => toCoreAngleState (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))
        ContDiffAt ℝ 1 F Y ∧ ∀ v : CoreAngleState,
          |(fderiv ℝ F Y v) 0 - v 0| ≤ (1040 + 512 * coreVariationBound) *
            (|v 1| / Y 0 + (Y 1 + Y 2) * (|v 0| + Y 0 * |v 1| + |v 2|) / Y 0) := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hentry : ContDiffAt ℝ 1 coreRadiusEntry Y :=
    contDiffAt_coreRadiusEntry 1 (by linarith only [hk])
  obtain ⟨T, hT, hfirst, hpos, hle, herr, σ, hσ, hcσ, hhit, huniq, hcP, _, hderiv⟩ :=
    exists_large_core_exit_derivative hk hu hw
  obtain ⟨S, _, hfirstS, hrad⟩ := exists_large_core_radius_variation hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  obtain ⟨R, _, hfirstR, hcore, _⟩ := exists_large_core_traversal hk hu hw
  have hRT : R = T := hfirstR.unique hfirst
  subst R
  let τ := fun Z => σ (coreRadiusEntry Z)
  let F := fun Z => toCoreAngleState (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))
  have hcτ : ContDiffAt ℝ 1 τ Y := hcσ.comp Y hentry
  have hcF : ContDiffAt ℝ 1 F Y := by convert! hcP.comp Y hentry using 1
  have hhit' : ∀ᶠ Z in 𝓝 Y, τ Z ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 (τ Z) 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 :=
    hentry.continuousAt.tendsto.eventually hhit
  have hpair : ContinuousAt (fun q : CoreAngleState × ℝ => (coreRadiusEntry q.1, q.2)) (Y, T) := by
    convert! (hentry.continuousAt.comp
      (continuousAt_fst : ContinuousAt (Prod.fst : CoreAngleState × ℝ → CoreAngleState) (Y, T))).prodMk
        continuousAt_snd using 1
  have huniq' : ∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, T),
      projectiveOriginalFlow (coreRadiusEntry q.1) 0 q.2 2 = 1 → τ q.1 = q.2 :=
    (hpair.eventually huniq).mono fun _ h => h.mp
  have hfirstNear := eventually_coreRadius_firstReturn hk hu hw hT hσ hcτ.continuousAt hfirst hcore
    (hhit'.mono fun _ h => h.2.2) huniq'
  refine ⟨T, hT, hfirst, τ, hσ, hcτ, hfirstNear, hcF, ?_⟩
  intro v
  let w := fderiv ℝ coreRadiusEntry Y v
  let ξ := fun t => coreProjectedFlowVariation (coreRadiusEntry Y) 0 t w
  let s := coreExitRadialFactor (projectiveOriginalFlow (coreRadiusEntry Y) 0 T)
  let Q₀ := |v 0| + Y 0 * |v 1| + |v 2|
  have hchain : HasFDerivAt F
      ((fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (σ z))) (coreRadiusEntry Y)).comp
        (fderiv ℝ coreRadiusEntry Y)) Y := by
    convert! ((hcP.differentiableAt (by norm_num)).hasFDerivAt).comp Y
      ((hentry.differentiableAt (by norm_num)).hasFDerivAt) using 1
  have hout : (fderiv ℝ F Y v) 0 = s * ξ T 0 := by
    rw [hchain.fderiv, ContinuousLinearMap.comp_apply]
    exact (hderiv w).2.1
  have hinit : ξ 0 = coreClockProjection (coreRadiusEntry Y) w :=
    coreProjectedFlowVariation_initial hD 0 w
  obtain ⟨hR, hX, _⟩ := coreRadiusEntry_variation_bounds hk hu hw v
  have hR' : |ξ 0 0 - v 0| ≤ 4 * (Y 1 / Y 0 + Y 2 ^ 2 / Y 0 ^ 2) * |v 0| := by
    rw [hinit]
    exact hR
  have hX' : |Y 0 * ξ 0 1| ≤ Y 0 * |v 1| + 4 * Y 0 * Y 1 * |v 0| := by
    rw [hinit]
    exact hX
  have hQ : |v 0| ≤ Q₀ := by
    dsimp [Q₀]
    have H := mul_nonneg hk0.le (abs_nonneg (v 1))
    linarith only [H, abs_nonneg (v 2)]
  have hWk : Y 2 ≤ Y 0 := by
    have H := coreBootstrap_wall_bound hk hw.2
    linarith only [H, hk]
  have H := core_radius_arrival_error hk hu.1 hw.1 hWk hQ hpos.le hle herr hR' hX'
    (hrad v T ⟨hT.le, le_rfl⟩)
  rw [hout]
  apply H.trans
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have hC : (256 : ℝ) ≤ 1040 + 512 * coreVariationBound := by linarith only [hK]
  calc
    _ = 256 * (|v 1| / Y 0) + (1040 + 512 * coreVariationBound) * ((Y 1 + Y 2) * Q₀ / Y 0) := by ring
    _ ≤ (1040 + 512 * coreVariationBound) * (|v 1| / Y 0) +
        (1040 + 512 * coreVariationBound) * ((Y 1 + Y 2) * Q₀ / Y 0) :=
      add_le_add (mul_le_mul_of_nonneg_right hC (div_nonneg (abs_nonneg _) hk0.le)) (le_refl _)
    _ = _ := by dsimp [Q₀]; ring
