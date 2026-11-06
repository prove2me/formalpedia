-- Prove2me | solution 1 for BianchiIX.exists_large_core_multiplier_differential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:05:26.904985+00:00
-- url     : https://prove2.me/submissions/72ae435b-cbe1-43af-b419-872d73e55a33

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_eventually_coreRadius_multiplier_formula
import Theorems.Thm_BianchiIX_exists_large_core_radius_arrival
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasFDerivAt_log_coreReturnMultiplier
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
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
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
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

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.coreFlowMultiplier_pos (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    0 < coreFlowMultiplier y t₀ a b i := Real.exp_pos _

end
end

/-- Differentiable positive factors for the genuine first-return map on an open neighborhood. -/
theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
      (∀ᶠ Z in 𝓝 Y,
        IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1) ∧
      ∀ i : Fin 2,
        0 < coreReturnMultiplier τ Y i ∧
        HasFDerivAt (fun Z => Real.log (coreReturnMultiplier τ Z i))
          (∫ s in (0 : ℝ)..1, (fderiv ℝ (coreRescaledLogRate τ i) (Y, s)).comp
            (ContinuousLinearMap.inl ℝ CoreAngleState ℝ)) Y ∧
        HasFDerivAt (fun Z => coreReturnMultiplier τ Z i)
          (coreReturnMultiplier τ Y i •
            ∫ s in (0 : ℝ)..1, (fderiv ℝ (coreRescaledLogRate τ i) (Y, s)).comp
              (ContinuousLinearMap.inl ℝ CoreAngleState ℝ)) Y := by
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, _⟩ := exists_large_core_radius_arrival hk hu hw
  obtain ⟨S, _, hfirstS, hcore, _⟩ := exists_large_core_traversal hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have hpos : 0 < τ Y := hτ ▸ hT
  have hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 :=
    fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0 :=
    fun t ht => (hcore t (hτ ▸ ht)).1
  have hregion : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) :=
    fun t ht => (hcore t (hτ ▸ ht)).2
  have hformula := eventually_coreRadius_multiplier_formula hk hD hcτ.continuousAt hpos hdom hA hregion
    (hnear.mono fun _ h => h.1.1.2)
  refine ⟨τ, hpos, hcτ, ?_, ?_⟩
  · filter_upwards [hnear, hformula] with Z hZ hf
    exact ⟨hZ.1, hf⟩
  · intro i
    have H := hasFDerivAt_log_coreReturnMultiplier hk hD hcτ hpos.le hdom hA hregion i
    refine ⟨coreFlowMultiplier_pos _ _ _ _ i, H, ?_⟩
    convert! H.exp using 1
    · ext Z
      exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm
    · rw [Real.exp_log (show 0 < coreReturnMultiplier τ Y i from coreFlowMultiplier_pos _ _ _ _ i)]
