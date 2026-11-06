-- Prove2me | solution 1 for BianchiIX.exists_large_core_log_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:08:17.786643+00:00
-- url     : https://prove2.me/submissions/800a4e0b-ef5a-4c8a-aa96-9eaa001d6740

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Theorems.Thm_BianchiIX_contDiffAt_log_coreReturnMultiplier
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreFlow_log_integral_bounds
import Theorems.Thm_BianchiIX_coreRadiusEntry_angle_fderiv
import Theorems.Thm_BianchiIX_coreRegion_log_rate_bounds
import Theorems.Thm_BianchiIX_coreReturn_exit_angle_bound
import Theorems.Thm_BianchiIX_coreReturn_log_derivative
import Theorems.Thm_BianchiIX_exists_large_core_entry_variation
import Theorems.Thm_BianchiIX_exists_large_core_multiplier_differential
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

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
open Set

private theorem BianchiIX.coreRadiusEntry_gap {k : ℝ} (hk : 6 ≤ k) : k / 2 ≤ Real.sqrt (k ^ 2 - 1) := by
  have hs := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ k ^ 2 - 1)
  have hnonneg := Real.sqrt_nonneg (k ^ 2 - 1)
  by_contra! hlt
  have H := (sq_lt_sq₀ hnonneg (by linarith only [hk] : 0 ≤ k / 2)).mpr hlt
  nlinarith only [hs, H, hk, sq_nonneg (k - 6)]

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

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.core_log_lower_bound {k : ℝ} (hk : 6 ≤ k) : 1 ≤ Real.log (4 * k) := by
  have H := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at H
  exact H.trans (Real.log_le_log (by norm_num) (by linarith only [hk]))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_angle_bound {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (v : CoreAngleState) :
    |fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v| ≤
      2 * |v 0| / Y 0 := by
  have hgap := coreRadiusEntry_gap hk
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hs : 0 < Real.sqrt (Y 0 ^ 2 - 1) := lt_of_lt_of_le (by positivity) hgap
  rw [coreRadiusEntry_angle_fderiv (by linarith only [hk]), abs_div, abs_neg, abs_of_pos hs]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hgap).trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_coreReturnMultiplier {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContDiffAt ℝ 1 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun Z => coreReturnMultiplier τ Z i) Y := by
  convert! (contDiffAt_log_coreReturnMultiplier hk hD hτ hpos hdom hA hcore i).exp using 1
  ext Z
  exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm

end
end

/-- Formula (B.33) for the actual first-return multipliers, with both moving endpoints. -/
theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
      (∀ᶠ Z in 𝓝 Y,
        IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1) ∧
      (∀ i : Fin 2, 0 < coreReturnMultiplier τ Y i ∧
        ContDiffAt ℝ 1 (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y ∧
        ContDiffAt ℝ 1 (fun Z => coreReturnMultiplier τ Z i) Y) ∧
      ∀ v : CoreAngleState,
        let Q₀ := |v 0| + Y 0 * |v 1| + |v 2|
        |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z 0)) Y v| ≤
          (20 * coreVariationBound + 4) * Real.log (4 * Y 0) * Q₀ ∧
        |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z 1)) Y v| ≤
          (118 * coreVariationBound + 8) * Real.log (4 * Y 0) * Q₀ / Y 0 ^ 2 := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨τ, hpos, hcτ, hnear, hmul⟩ := exists_large_core_multiplier_differential hk hu hw
  have hfirst := hnear.self_of_nhds.1
  obtain ⟨T, _, hfirstT, hcoreT, hM, _⟩ := exists_large_core_traversal hk hu hw
  have hT : T = τ Y := hfirstT.unique hfirst
  subst T
  obtain ⟨S, _, hfirstS, _, hnorm⟩ := exists_large_core_entry_variation hk hu hw
  have hS : S = τ Y := hfirstS.unique hfirst
  subst S
  have hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 :=
    fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0 :=
    fun t ht => (hcoreT t ht).1
  have hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) :=
    fun t ht => (hcoreT t ht).2
  have hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Y) 0 0)) = Y 0 := by
    rw [projectiveOriginalFlow_initial hD, projectiveCoreAngle,
      cosh_coreAngle (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num),
      coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)]
    exact div_one _
  refine ⟨τ, hpos, hcτ, hnear, fun i => ⟨(hmul i).1,
    contDiffAt_log_coreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i,
    contDiffAt_coreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i⟩, ?_⟩
  intro v Q₀
  let Q := (2 * coreVariationBound) * Q₀
  let β := projectiveOriginalFlow (coreRadiusEntry Y) 0
  let w := fderiv ℝ coreRadiusEntry Y v
  let ξ := fun t => coreProjectedFlowVariation (coreRadiusEntry Y) 0 t w
  let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t))
  let I := fun i : Fin 2 => ∫ t in 0..τ Y, coreOriginalClockRate (β t) *
    (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t)) (ξ t)) i
  let a := fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v
  let b := fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v
  have hQ₀ : 0 ≤ Q₀ := by dsimp [Q₀]; positivity
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg (by norm_num) hK) hQ₀
  have hnorm' (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) : ‖scaleCoreVariation (Y 0) (ξ t)‖ ≤ Q := hnorm t ht v
  have hend : τ Y ∈ Icc 0 (τ Y) := ⟨hpos.le, le_rfl⟩
  have hstart : (0 : ℝ) ∈ Icc 0 (τ Y) := ⟨le_rfl, hpos.le⟩
  have hI : |I 0| ≤ 6 * Real.log (4 * Y 0) * Q ∧
      |I 1| ≤ 51 * Real.log (4 * Y 0) * Q / Y 0 ^ 2 :=
    coreFlow_log_integral_bounds hk hpos.le hD hdom hA hcore hentry w hnorm'
  have hv0 : |v 0| ≤ Q₀ := by
    dsimp [Q₀]
    linarith only [mul_nonneg hk0.le (abs_nonneg (v 1)), abs_nonneg (v 2)]
  have ha : |a| ≤ 2 * Q₀ / Y 0 := (coreRadiusEntry_angle_bound hk v).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv0 (by norm_num)) hk0.le)
  have hb : |b| ≤ 2 * Q / Y 0 := by
    have H := coreReturn_exit_angle_bound hk hD hcτ.continuousAt (hdom hend) (hA _ hend)
      (hcore _ hend) (hnear.mono fun _ h => h.1.1.2) hM v
    have hr : |ξ (τ Y) 0| ≤ Q :=
      (norm_le_pi_norm (scaleCoreVariation (Y 0) (ξ (τ Y))) 0).trans (hnorm' _ hend)
    exact H.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num)) hk0.le)
  have hLa := coreRegion_log_rate_bounds hk (hcore 0 hstart)
  have hLb := coreRegion_log_rate_bounds hk (hcore (τ Y) hend)
  have ha0 : |L 0 0 * a| ≤ 4 * Q₀ := by
    rw [abs_mul]
    exact (mul_le_mul hLa.1 ha (abs_nonneg _) (by positivity)).trans_eq (by field_simp; ring)
  have hb0 : |L (τ Y) 0 * b| ≤ 4 * Q := by
    rw [abs_mul]
    exact (mul_le_mul hLb.1 hb (abs_nonneg _) (by positivity)).trans_eq (by field_simp; ring)
  have ha1 : |L 0 1 * a| ≤ 8 * Q₀ / Y 0 ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hLa.2.1 ha (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hb1 : |L (τ Y) 1 * b| ≤ 8 * Q / Y 0 ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hLb.2.1 hb (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hderiv (i : Fin 2) :
      fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v = I i + L (τ Y) i * b - L 0 i * a :=
    coreReturn_log_derivative hk hD hcτ hpos.le hdom hA hcore v i
  have htri (i : Fin 2) :
      |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v| ≤
        |I i| + |L (τ Y) i * b| + |L 0 i * a| := by
    rw [hderiv]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
  have hlogQ : Q ≤ Real.log (4 * Y 0) * Q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (core_log_lower_bound hk) hQ
  have hlogQ₀ : Q₀ ≤ Real.log (4 * Y 0) * Q₀ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (core_log_lower_bound hk) hQ₀
  constructor
  · apply (htri 0).trans ((add_le_add (add_le_add hI.1 hb0) ha0).trans ?_)
    calc
      _ ≤ 10 * Real.log (4 * Y 0) * Q + 4 * Real.log (4 * Y 0) * Q₀ := by
        nlinarith only [hlogQ, hlogQ₀]
      _ = _ := by dsimp [Q]; ring
  · apply (htri 1).trans ((add_le_add (add_le_add hI.2 hb1) ha1).trans ?_)
    calc
      _ = (51 * Real.log (4 * Y 0) * Q + 8 * Q + 8 * Q₀) / Y 0 ^ 2 := by ring
      _ ≤ (59 * Real.log (4 * Y 0) * Q + 8 * Real.log (4 * Y 0) * Q₀) / Y 0 ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith only [hlogQ, hlogQ₀]) (sq_nonneg _)
      _ = _ := by dsimp [Q]; ring
