-- Prove2me | solution 1 for BianchiIX.exists_angularRegion_statistics
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:59:14.011408+00:00
-- url     : https://prove2.me/submissions/ee8a75e2-1078-4b35-874c-677a917345d3

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_RestartFluxData
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalFutureData
import Definitions.Def_BianchiIX_RadialFailureData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_era_joint_statistics
import Theorems.Thm_BianchiIX_exists_restartConnection_output_bounds
import Theorems.Thm_BianchiIX_exists_restartConnection_output_phase
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartRadialCurve_control
import Theorems.Thm_BianchiIX_exists_restart_statistical_preparation
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_cutoff_budget (C C₀ q : ℝ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, (0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
      C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 := by
  have HI : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun ρ : ℝ => ρ * Real.log ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HB : Tendsto (fun ρ : ℝ => 2 * C₀ * ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using HI.const_mul (2 * C₀)
  have HT : Tendsto (fun ρ : ℝ => C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    convert! HL.const_mul (-C * C₀ * q) using 1
    · ext ρ
      rw [one_div, Real.log_inv]
      ring
    · simp
  filter_upwards [show ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ from self_mem_nhdsWithin,
    HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with ρ hρ hρ1 hb ht
  exact ⟨⟨hρ, hρ1.le⟩, hb.le, ht.le⟩

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped ENNReal

private theorem BianchiIX.lintegral_three_coordinates {f : (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z) = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ r : ℝ, f ![r, x, y] := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1
  have he : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1)
  rw [← he.lintegral_comp hf]
  change (∫⁻ p, (f ∘ e.symm) p ∂(volume.prod volume)) = _
  rw [lintegral_prod _ (hf.comp e.symm.measurable).aemeasurable]
  apply lintegral_congr
  intro x
  let g := fun v : Fin 2 → ℝ => f (e.symm (x, v))
  have hg : Measurable g := hf.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
  let e₂ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he₂ : MeasurePreserving e₂.symm volume volume :=
    MeasurePreserving.symm e₂ (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
  change (∫⁻ v, g v) = _
  rw [← he₂.lintegral_comp hg]
  change (∫⁻ p, (g ∘ e₂.symm) p ∂(volume.prod volume)) = _
  rw [lintegral_prod_symm _ (hg.comp e₂.symm.measurable).aemeasurable]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro r
  change f (e.symm (x, e₂.symm (r, y))) = f ![r, x, y]
  apply congrArg f
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.clippedPowerDensity_nonneg {ell B δ x : ℝ} (hl : 0 ≤ ell) (hB : 0 ≤ B)
    (hx : 0 ≤ x) : 0 ≤ clippedPowerDensity ell B δ x :=
  div_nonneg (le_min hl (mul_nonneg hB (Real.rpow_nonneg hx δ))) hx

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.measurable_clippedPowerDensity {δ : ℝ} (hδ : 0 ≤ δ) (ell B : ℝ) :
    Measurable (clippedPowerDensity ell B δ) :=
  (measurable_const.min (measurable_const.mul (Real.continuous_rpow_const hδ).measurable)).div
    measurable_id

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.clippedPowerDensity_le {ell B δ x : ℝ} (hx : 0 < x) :
    clippedPowerDensity ell B δ x ≤ B * x ^ (δ - 1) := by
  calc
    clippedPowerDensity ell B δ x ≤ B * x ^ δ / x := div_le_div_of_nonneg_right (min_le_right _ _) hx.le
    _ = B * x ^ (δ - 1) := by rw [Real.rpow_sub hx, Real.rpow_one]; ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.intervalIntegrable_clippedPowerDensity {ell B δ r : ℝ}
    (hl : 0 ≤ ell) (hB : 0 ≤ B) (hδ : 0 < δ) (hr : 0 ≤ r) :
    IntervalIntegrable (clippedPowerDensity ell B δ) volume 0 r := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr]
  have H : IntegrableOn (fun x : ℝ => B * x ^ (δ - 1)) (Ioo 0 r) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hr).mp
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < δ - 1)).const_mul B)
  refine H.mono' (measurable_clippedPowerDensity hδ.le ell B).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (clippedPowerDensity_nonneg hl hB hx.1.le)]
  exact clippedPowerDensity_le hx.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.integral_power_density {δ : ℝ} (hδ : 0 < δ) (B r : ℝ) :
    (∫ x in (0 : ℝ)..r, B * x ^ (δ - 1)) = B * r ^ δ / δ := by
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < δ - 1))]
  simp only [sub_add_cancel, Real.zero_rpow (ne_of_gt hδ), sub_zero]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.clippedPowerDensity_below {ell B δ x c : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hx : 0 < x) (hxc : x ≤ c) (hc : B * c ^ δ = ell) :
    clippedPowerDensity ell B δ x = B * x ^ (δ - 1) := by
  have H : B * x ^ δ ≤ ell := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxc hδ) hB
  rw [clippedPowerDensity, min_eq_right H, Real.rpow_sub hx, Real.rpow_one]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.clippedPowerDensity_above {ell B δ x c : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hc0 : 0 ≤ c) (hcx : c ≤ x) (hc : B * c ^ δ = ell) :
    clippedPowerDensity ell B δ x = ell / x := by
  have H : ell ≤ B * x ^ δ := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc0 hcx hδ) hB
  exact congrArg (fun z => z / x) (min_eq_left H)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.integral_clippedPowerDensity_of_cutoff {ell B δ c : ℝ}
    (hl : 0 ≤ ell) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : B * c ^ δ = ell) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) = ell / δ + ell * Real.log (1 / c) := by
  have hi0c := intervalIntegrable_clippedPowerDensity hl hB hδ hc0.le
  have hi01 := intervalIntegrable_clippedPowerDensity hl hB hδ (by norm_num : (0 : ℝ) ≤ 1)
  have hleft : (∫ x in (0 : ℝ)..c, clippedPowerDensity ell B δ x) = ell / δ := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hc0.le
      (fun x hx => clippedPowerDensity_below hB hδ.le hx.1 hx.2.le hc),
      integral_power_density hδ, hc]
  have hright : (∫ x in c..(1 : ℝ), clippedPowerDensity ell B δ x) = ell * Real.log (1 / c) := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hc1
      (fun x hx => clippedPowerDensity_above hB hδ.le hc0.le hx.1.le hc)]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hc0 (by norm_num)]
    simp only [one_div, one_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0c (hi0c.symm.trans hi01), hleft, hright]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.integral_clippedPowerDensity_of_le {ell B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 < δ) (hBl : B ≤ ell) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) = B / δ := by
  calc
    _ = ∫ x in (0 : ℝ)..1, B * x ^ (δ - 1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      have hp : B * x ^ δ ≤ ell :=
        (mul_le_of_le_one_right hB (Real.rpow_le_one hx.1.le hx.2.le hδ.le)).trans hBl
      dsimp only
      rw [clippedPowerDensity, min_eq_right hp, Real.rpow_sub hx.1, Real.rpow_one]
      ring
    _ = B / δ := by rw [integral_power_density hδ]; simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.integral_clippedPowerDensity {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) =
      min ell B / δ * (1 + max (Real.log (B / ell)) 0) := by
  by_cases hBl : B ≤ ell
  · have heq := integral_clippedPowerDensity_of_le hB.le hδ hBl
    have hlog : Real.log (B / ell) ≤ 0 :=
      Real.log_nonpos (div_nonneg hB.le hl.le) ((div_le_one hl).mpr hBl)
    rw [heq, min_eq_right hBl, max_eq_right hlog]
    ring
  · have hlB : ell ≤ B := (lt_of_not_ge hBl).le
    let c : ℝ := (ell / B) ^ δ⁻¹
    have hc0 : 0 < c := Real.rpow_pos_of_pos (div_pos hl hB) _
    have hc1 : c ≤ 1 := Real.rpow_le_one (div_nonneg hl.le hB.le)
      ((div_le_one hB).mpr hlB) (inv_nonneg.mpr hδ.le)
    have hc : B * c ^ δ = ell := by
      dsimp only [c]
      rw [Real.rpow_inv_rpow (div_nonneg hl.le hB.le) (ne_of_gt hδ)]
      field_simp
    have hlogc : Real.log (1 / c) = Real.log (B / ell) / δ := by
      rw [one_div, Real.log_inv]
      dsimp only [c]
      rw [Real.log_rpow (div_pos hl hB),
        Real.log_div (ne_of_gt hl) (ne_of_gt hB), Real.log_div (ne_of_gt hB) (ne_of_gt hl)]
      ring
    have hlog : 0 ≤ Real.log (B / ell) := Real.log_nonneg ((one_le_div hl).mpr hlB)
    rw [integral_clippedPowerDensity_of_cutoff hl.le hB.le hδ hc0 hc1 hc,
      hlogc, min_eq_left hlB, max_eq_left hlog]
    ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.lintegral_unit_ofReal_eq {f : ℝ → ℝ}
    (hi : IntervalIntegrable f volume 0 1) (hn : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (f x)) = ENNReal.ofReal (∫ x in (0 : ℝ)..1, f x) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hi
  · exact ae_restrict_of_forall_mem measurableSet_Ioo hn

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.lintegral_clipped_log_one {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (min ell (B * x ^ δ) / x)) =
      ENNReal.ofReal (min ell B / δ * (1 + max (Real.log (B / ell)) 0)) := by
  exact (lintegral_unit_ofReal_eq (intervalIntegrable_clippedPowerDensity hl.le hB.le hδ (by norm_num))
    (fun _ hx => clippedPowerDensity_nonneg hl.le hB.le hx.1.le)).trans
      (congrArg ENNReal.ofReal (integral_clippedPowerDensity hl hB hδ))

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.hasSum_dyadic_weights : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) 1 := by
  convert! hasSum_geometric_two.mul_left (1 / 2 : ℝ) using 1
  · ext j
    rw [pow_succ]
    ring
  · norm_num

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.hasSum_dyadic_first_moment :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1)) 2 := by
  have H : HasSum (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) using 1
    norm_num
  convert! (H.add hasSum_geometric_two).mul_left (1 / 2 : ℝ) using 1
  · ext j
    rw [pow_succ]
    ring
  · norm_num

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < dyadicScale d j := by
  exact mul_pos hd (pow_pos (by norm_num) _)

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_le {d : ℝ} (hd : 0 ≤ d) (j : ℕ) : dyadicScale d j ≤ d :=
  mul_le_of_le_one_right hd (pow_le_one₀ (by norm_num) (by norm_num))

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.log_dyadicScale {d : ℝ} (hd : 0 < d) (j : ℕ) :
    Real.log (dyadicScale d j) = Real.log d - ((j : ℝ) + 1) * Real.log 2 := by
  rw [dyadicScale, Real.log_mul (ne_of_gt hd) (ne_of_gt (pow_pos (by norm_num) _)), Real.log_pow]
  simp only [Nat.cast_add, Nat.cast_one, one_div, Real.log_inv]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radial_phase_deleted_length {f : ℝ → ℝ} {a b c : ℝ} {A E : Set ℝ}
    (hc : 0 < c) (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hder : ∀ x ∈ Icc a b, c ≤ deriv f x)
    (hA : MeasurableSet A) (hAI : A ⊆ Icc a b) (hE : f '' A ⊆ E) :
    volume A ≤ min (ENNReal.ofReal (b - a)) (ENNReal.ofReal (1 / c) * volume E) := by
  have hmono : StrictMonoOn f (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => hc.trans_le (hder x (interior_subset hx)))
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun x hx => (hf x (hAI hx)).hasDerivAt.hasDerivWithinAt)
    (hmono.injOn.mono hAI) (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, mul_one, Measure.restrict_apply_univ] at hj
  have hscale : ENNReal.ofReal c * volume A ≤ volume (f '' A) := by
    calc
      _ = ∫⁻ _ in A, ENNReal.ofReal c := by simp
      _ ≤ ∫⁻ x in A, ENNReal.ofReal |deriv f x| :=
        setLIntegral_mono' hA (fun x hx => ENNReal.ofReal_le_ofReal
          ((hder x (hAI hx)).trans (le_abs_self _)))
      _ = _ := hj.symm
  refine le_min ?_ ?_
  · simpa only [Real.volume_Icc] using (measure_mono hAI : volume A ≤ volume (Icc a b))
  · calc
      volume A = ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * volume A) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hc.ne']
        simp
      _ ≤ ENNReal.ofReal (1 / c) * volume E :=
        mul_le_mul' le_rfl (hscale.trans (measure_mono hE))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.two_mul_dyadicScale (d : ℝ) (j : ℕ) :
    2 * dyadicScale d j = d * (1 / 2 : ℝ) ^ j := by
  rw [dyadicScale, pow_succ]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_mem_dyadicScale_Ioc {d x : ℝ} (hd : 0 < d) (hx : x ∈ Ioc 0 d) :
    ∃ j : ℕ, x ∈ Ioc (dyadicScale d j) (2 * dyadicScale d j) := by
  obtain ⟨j, hj, hJ⟩ := exists_nat_pow_near_of_lt_one (div_pos hx.1 hd)
    ((div_le_one hd).mpr hx.2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j, ?_, ?_⟩
  · change d * (1 / 2 : ℝ) ^ (j + 1) < x
    exact (mul_comm _ _).trans_lt ((lt_div_iff₀ hd).mp hj)
  · rw [two_mul_dyadicScale]
    exact ((div_le_iff₀ hd).mp hJ).trans_eq (mul_comm _ _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.iUnion_dyadicScale_Ioc {d : ℝ} (hd : 0 < d) :
    (⋃ j : ℕ, Ioc (dyadicScale d j) (2 * dyadicScale d j)) = Ioc 0 d := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    refine ⟨(dyadicScale_pos hd j).trans hj.1, hj.2.trans ?_⟩
    rw [two_mul_dyadicScale]
    exact mul_le_of_le_one_right hd.le (pow_le_one₀ (by norm_num) (by norm_num))
  · intro hx
    obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd hx
    exact mem_iUnion_of_mem j hj

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped ENNReal

private theorem BianchiIX.hasSum_dyadic_log_abs {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    HasSum (fun j => dyadicScale d j * |Real.log (dyadicScale d j)|)
      (d * (|Real.log d| + 2 * Real.log 2)) := by
  have H := (hasSum_dyadic_weights.mul_left |Real.log d|).add
    (hasSum_dyadic_first_moment.mul_left (Real.log 2))
  convert! H.mul_left d using 1
  · ext j
    rw [abs_of_nonpos (Real.log_nonpos (dyadicScale_pos hd j).le ((dyadicScale_le hd.le j).trans hd1)),
      log_dyadicScale hd, abs_of_nonpos (Real.log_nonpos hd.le hd1)]
    dsimp only [dyadicScale]
    ring
  · ring

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped ENNReal

private theorem BianchiIX.dyadic_log_flux_sum {d C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C) :
    (∑' j, ENNReal.ofReal (C * (dyadicScale d j * |Real.log (dyadicScale d j)|))) =
      ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg hC (mul_nonneg (dyadicScale_pos hd j).le (abs_nonneg _)))
    ((hasSum_dyadic_log_abs hd hd1).summable.mul_left C), tsum_mul_left,
    (hasSum_dyadic_log_abs hd hd1).tsum_eq]
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_radial_failure {f : ℝ → ℝ} {a b : ℝ} {A G : Set ℝ}
    (hf : ContinuousOn f (Icc a b)) (hA : MeasurableSet A) (hAI : A ⊆ Icc a b)
    (hG : MeasurableSet G) : MeasurableSet (A \ f ⁻¹' G) := by
  have hm : Measurable (fun p : A => f p.val) := (hf.mono hAI).domRestrict.measurable
  have heq : A \ f ⁻¹' G = Subtype.val '' {p : A | f p.val ∉ G} := by
    ext x
    constructor
    · exact fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
  rw [heq]
  exact hA.subtype_image (hG.compl.preimage hm)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radial_phase_deleted_weighted {f : ℝ → ℝ} {a b c M : ℝ} {A F E : Set ℝ}
    {ω : ℝ → ℝ≥0∞} (hc : 0 < c) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x) (hder : ∀ x ∈ Icc a b, c ≤ deriv f x)
    (hF : MeasurableSet F) (hFA : F ⊆ A) (hAI : A ⊆ Icc a b) (hE : f '' F ⊆ E)
    (hω : ∀ x ∈ A, ω x ≤ ENNReal.ofReal M) :
    (∫⁻ x in F, ω x) ≤ min (∫⁻ x in A, ω x) (ENNReal.ofReal (M / c) * volume E) := by
  have hlen := (radial_phase_deleted_length hc hf hder hF (hFA.trans hAI) hE).trans (min_le_right _ _)
  refine le_min (lintegral_mono_set hFA) ?_
  calc
    (∫⁻ x in F, ω x) ≤ ∫⁻ _ in F, ENNReal.ofReal M := setLIntegral_mono' hF (fun x hx => hω x (hFA hx))
    _ = ENNReal.ofReal M * volume F := by simp
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal (1 / c) * volume E) := mul_le_mul' le_rfl hlen
    _ = ENNReal.ofReal (M / c) * volume E := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hM]
      congr 2
      ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radial_phase_failure_weighted {f : ℝ → ℝ} {a b c M L : ℝ} {A G : Set ℝ}
    {ω : ℝ → ℝ≥0∞} (hc : 0 < c) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x) (hder : ∀ x ∈ Icc a b, c ≤ deriv f x)
    (hA : MeasurableSet A) (hAI : A ⊆ Icc a b) (hunit : ∀ x ∈ A, f x ∈ Ioo 0 1)
    (hG : MeasurableSet G) (hloss : volume (Ioo 0 1 \ G) ≤ ENNReal.ofReal L)
    (hω : ∀ x ∈ A, ω x ≤ ENNReal.ofReal M) :
    MeasurableSet (A \ f ⁻¹' G) ∧
      (∫⁻ x in A \ f ⁻¹' G, ω x) ≤
        min (∫⁻ x in A, ω x) (ENNReal.ofReal (M / c) * ENNReal.ofReal L) := by
  have hF := measurableSet_radial_failure (fun x hx => (hf x hx).continuousAt.continuousWithinAt) hA hAI hG
  refine ⟨hF, ?_⟩
  have himage : f '' (A \ f ⁻¹' G) ⊆ Ioo 0 1 \ G := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hunit x hx.1, hx.2⟩
  exact (radial_phase_deleted_weighted hc hM hf hder hF sdiff_subset hAI himage hω).trans
    (min_le_min_left _ (mul_le_mul' le_rfl hloss))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.wallAmplitude_le_square {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hba : b ≤ a) (hca : c ≤ a) : wallAmplitude a b c ≤ a ^ 2 := by
  have hp : a * b * c ≤ a ^ 3 := by
    calc
      a * b * c ≤ a * a * a :=
        mul_le_mul (mul_le_mul_of_nonneg_left hba ha) hca hc (mul_nonneg ha ha)
      _ = a ^ 3 := by ring
  unfold wallAmplitude
  calc
    _ ≤ (a ^ 3) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg (mul_nonneg ha hb) hc) hp (by norm_num)
    _ = a ^ 2 := by rw [← Real.rpow_natCast_mul ha]; norm_num

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.small_section_bounds {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    curvature h b c ≤ (25 / 16) * h ^ 2 ∧
      (983 / 1024 : ℝ) ≤ p ^ 2 ∧ p ≤ -15 / 16 ∧ shearSq p s ≤ 2 := by
  have hsum : h + b + c ≤ 5 / 4 * h := by linarith
  have hsum2 := pow_le_pow_left₀ (by linarith : 0 ≤ h + b + c) hsum 2
  have hcurv := abs_le.mp (curvature_abs_le_sum_sq hh.le hb hc)
  have hQ : curvature h b c ≤ (25 / 16) * h ^ 2 := by nlinarith
  have hQlo : -(25 / 16) * h ^ 2 ≤ curvature h b c := by nlinarith
  have hh2 : h ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hh.le hh1 2
  have hs2 : s ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hs)
  have hcon : p ^ 2 + s ^ 2 + curvature h b c = 1 := hconstraint
  have hp2 : (983 / 1024 : ℝ) ≤ p ^ 2 := by nlinarith
  refine ⟨hQ, hp2, ?_, ?_⟩
  · nlinarith [sq_nonneg (p + 15 / 16)]
  · unfold shearSq
    nlinarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sectionFluxDensity_eq {p s : ℝ} (hp : p < 0) :
    sectionFluxDensity p s = 1 + shearSq p s / (2 * |p|) := by
  rw [sectionFluxDensity, abs_of_neg hp]
  field_simp [ne_of_lt hp]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.small_section_flux_bounds {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    1 ≤ sectionFluxDensity p s ∧ sectionFluxDensity p s ≤ 3 := by
  obtain ⟨_, _, hpbound, hS⟩ := small_section_bounds hh hh1 hb hc hb1 hc1 hs hp hconstraint
  have habs : 15 / 16 ≤ |p| := by rw [abs_of_neg hp]; linarith
  have hden : 0 < 2 * |p| := by positivity
  have hS0 : 0 ≤ shearSq p s := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [sectionFluxDensity_eq hp]
  constructor
  · linarith [div_nonneg hS0 hden.le]
  · have H : shearSq p s / (2 * |p|) ≤ 2 :=
      (div_le_iff₀ hden).mpr (by linarith)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.small_section_corrected_flux_bounds {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    (1 / 2 : ℝ) ≤ correctedSectionFluxDensity p s h b c ∧
      correctedSectionFluxDensity p s h b c ≤ sectionFluxDensity p s ∧
      correctedSectionFluxDensity p s h b c ≤ 3 := by
  have hflux := small_section_flux_bounds hh hh1 hb hc hb1 hc1 hs hp hconstraint
  have hH0 : 0 ≤ wallAmplitude h b c := Real.rpow_nonneg (mul_nonneg (mul_nonneg hh.le hb) hc) _
  have hH : wallAmplitude h b c ≤ h ^ 2 := wallAmplitude_le_square hh.le hb hc (by linarith) (by linarith)
  have hh2 := pow_le_pow_left₀ hh.le hh1 2
  have hden : 0 < 1 + 4 * wallAmplitude h b c := by positivity
  have hlow : (1 / 2 : ℝ) ≤ correctedSectionFluxDensity p s h b c := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hup : correctedSectionFluxDensity p s h b c ≤ sectionFluxDensity p s := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ sectionFluxDensity p s) hH0]
  exact ⟨hlow, hup, hup.trans hflux.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmicFluxConstantOne_nonneg {C σ : ℝ} (hC : 1 ≤ C) (hσ : 0 < σ) :
    0 ≤ logarithmicFluxConstantOne C σ := by
  have H := Real.log_nonneg hC
  unfold logarithmicFluxConstantOne
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmicLayerCostOne_le {a C σ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 1 ≤ C) (hσ : 0 < σ) :
    logarithmicLayerCostOne a C σ ≤
      ENNReal.ofReal (logarithmicFluxConstantOne C σ * a * (1 + |Real.log a|)) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hB : 0 < C * a ^ (-2 * σ) := mul_pos hC0 (Real.rpow_pos_of_pos ha _)
  have hlogC := Real.log_nonneg hC
  have hloga := Real.log_nonpos ha.le ha1
  have hlogs : Real.log (C * a ^ (-2 * σ) / a) = Real.log C + (1 + 2 * σ) * |Real.log a| := by
    rw [Real.log_div hB.ne' ha.ne', Real.log_mul hC0.ne' (Real.rpow_pos_of_pos ha _).ne',
      Real.log_rpow ha, abs_of_nonpos hloga]
    ring
  unfold logarithmicLayerCostOne
  rw [lintegral_clipped_log_one ha hB hσ, hlogs, max_eq_left (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have H : 1 + (Real.log C + (1 + 2 * σ) * |Real.log a|) ≤
      (1 + Real.log C + 2 * σ) * (1 + |Real.log a|) := by
    nlinarith [mul_nonneg hlogC (abs_nonneg (Real.log a))]
  calc
    _ ≤ a / σ * (1 + (Real.log C + (1 + 2 * σ) * |Real.log a|)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_left _ _) hσ.le) (by positivity)
    _ ≤ a / σ * ((1 + Real.log C + 2 * σ) * (1 + |Real.log a|)) :=
      mul_le_mul_of_nonneg_left H (div_nonneg ha.le hσ.le)
    _ = _ := by unfold logarithmicFluxConstantOne; ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.dyadic_log_one_flux_sum {d C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C) :
    (∑' j, ENNReal.ofReal (C * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|)))) =
      ENNReal.ofReal (C * d * (1 + |Real.log d| + 2 * Real.log 2)) := by
  have H : HasSum (fun j => dyadicScale d j * (1 + |Real.log (dyadicScale d j)|))
      (d * (1 + |Real.log d| + 2 * Real.log 2)) := by
    convert! (hasSum_dyadic_weights.mul_left d).add (hasSum_dyadic_log_abs hd hd1) using 1
    · ext j
      dsimp only [dyadicScale]
      ring
    · ring
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg hC (mul_nonneg (dyadicScale_pos hd j).le (by positivity))) (H.summable.mul_left C),
    tsum_mul_left, H.tsum_eq]
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_mainWallRadicand (h : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (mainWallRadicand h) := by
  unfold mainWallRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isOpen_mainWallChartDomain (h : ℝ) : IsOpen (mainWallChartDomain h) :=
  isOpen_lt continuous_const (contDiff_mainWallRadicand h 1).continuous

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_constraint {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : stateConstraint (mainWallChart h y) = 1 := by
  have H := Real.sq_sqrt hy.le
  dsimp [stateConstraint, constraint, shearSq, mainWallChart]
  rw [neg_sq, H]
  unfold mainWallRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_negative {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : mainWallChart h y 0 < 0 :=
  neg_neg_of_pos (Real.sqrt_pos.mpr hy)

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
open Set

private theorem BianchiIX.mainWallReflection_det : mainWallReflectionEquiv.toLinearMap.det = 1 := by
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' mainWallReflectionEquiv.toLinearMap =
      !![-1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, mainWallReflectionEquiv, mainWallReflectionLinear, mainWallReflection]
  rw [H]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallRadicand_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallRadicand h (mainWallReflection y) = mainWallRadicand h y := by
  dsimp [mainWallRadicand, mainWallReflection, curvature]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChart_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallChart h (mainWallReflection y) = axisSwap (mainWallChart h y) := by
  simp only [mainWallChart, mainWallRadicand_reflection]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChartDensity_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallChartDensity h (mainWallReflection y) = mainWallChartDensity h y := by
  unfold mainWallChartDensity
  rw [mainWallChart_reflection]
  dsimp [axisSwap, mainWallReflection, correctedSectionFluxDensity, sectionFluxDensity, shearSq, wallAmplitude]
  rw [neg_sq, show h * Real.exp (-y 2) * Real.exp (-y 1) = h * Real.exp (-y 1) * Real.exp (-y 2) by ring]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedMaxDomain_mainWallReflection (h t₀ : ℝ) (y : SectionCoordinates) :
    normalizedMaxDomain (mainWallChart h (mainWallReflection y)) t₀ =
      normalizedMaxDomain (mainWallChart h y) t₀ := by
  rw [mainWallChart_reflection]
  exact NormalizedSymmetry.swap.maxDomain _ _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedMaxCurve_mainWallReflection {h t₀ t : ℝ} {y : SectionCoordinates}
    (ht : t ∈ normalizedMaxDomain (mainWallChart h y) t₀) :
    normalizedMaxCurve (mainWallChart h (mainWallReflection y)) t₀ t =
      axisSwap (normalizedMaxCurve (mainWallChart h y) t₀ t) := by
  rw [mainWallChart_reflection]
  exact NormalizedSymmetry.swap.maxCurve ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.hasFDerivAt_scaledAngularLogCoordinates {a : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hρ : 0 < z 0) (ht : 0 < z 2) :
    HasFDerivAt (scaledAngularLogCoordinates a) (scaledAngularLogDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z) using 1
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z).log hρ.ne').neg using 1
    ext v
    change -(z 0)⁻¹ * v 0 = -((z 0)⁻¹ * v 0)
    ring
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).const_mul (2 * a)).log
      (mul_pos (mul_pos (by norm_num) ha) ht).ne').neg
    convert! H using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((2 * a * z 2)⁻¹ * (2 * a * v 2))
    field_simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledAngularLogDifferential_det {z : SectionCoordinates} (hρ : z 0 ≠ 0) :
    (scaledAngularLogDifferential z).det = -(z 2)⁻¹ := by
  change (scaledAngularLogDifferential z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' (scaledAngularLogDifferential z).toLinearMap =
      !![z 1, z 0, 0; -(z 0)⁻¹, 0, 0; 0, 0, -(z 2)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, scaledAngularLogDifferential]
  rw [H]
  simp [Matrix.det_fin_three, mul_comm, hρ]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledAngularLogCoordinates_injOn {a : ℝ} (ha : 0 < a) :
    InjOn (scaledAngularLogCoordinates a) {z : SectionCoordinates | 0 < z 0 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change -Real.log (z 0) = -Real.log (w 0) at h1
  change -Real.log (2 * a * z 2) = -Real.log (2 * a * w 2) at h2
  have hρ := Real.log_injOn_pos hz.1 hw.1 (neg_injective h1)
  have ht := Real.log_injOn_pos (mul_pos (mul_pos (by norm_num) ha) hz.2)
    (mul_pos (mul_pos (by norm_num) ha) hw.2) (neg_injective h2)
  have htw : z 2 = w 2 := mul_left_cancel₀ (by positivity : 2 * a ≠ 0) ht
  change z 1 * z 0 = w 1 * w 0 at h0
  rw [hρ] at h0
  have hθ := mul_right_cancel₀ hw.1.ne' h0
  ext i
  fin_cases i
  · exact hρ
  · exact hθ
  · exact htw

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_scaledAngularLogCoordinates {a : ℝ} {A : Set SectionCoordinates}
    (ha : 0 < a) (hA : MeasurableSet A) (hpos : ∀ z ∈ A, 0 < z 0 ∧ 0 < z 2) :
    volume (scaledAngularLogCoordinates a '' A) = ∫⁻ z in A, ENNReal.ofReal (1 / z 2) := by
  have hd (z : SectionCoordinates) (hz : z ∈ A) :=
    hasFDerivAt_scaledAngularLogCoordinates ha (hpos z hz).1 (hpos z hz).2
  have hi : InjOn (scaledAngularLogCoordinates a) A := (scaledAngularLogCoordinates_injOn ha).mono hpos
  have H := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA
    (fun z hz => (hd z hz).hasFDerivWithinAt) hi (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at H
  rw [H]
  apply setLIntegral_congr_fun hA
  intro z hz
  change ENNReal.ofReal |(scaledAngularLogDifferential z).det| = ENNReal.ofReal (1 / z 2)
  rw [scaledAngularLogDifferential_det (hpos z hz).1.ne', abs_neg,
    abs_of_pos (inv_pos.mpr (hpos z hz).2), one_div]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_mainWallReflection_image {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    MeasurableSet (mainWallReflection '' A) :=
  hA.image_of_continuousOn_injOn mainWallReflectionEquiv.continuous.continuousOn
    mainWallReflectionEquiv.injective.injOn

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_reflection {h : ℝ} {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    mainWallMeasure h (mainWallReflection '' A) = mainWallMeasure h A := by
  let D := mainWallChartDomain h
  have hD : MeasurableSet D := (isOpen_mainWallChartDomain h).measurableSet
  have hI : mainWallReflection '' (A ∩ D) = mainWallReflection '' A ∩ D := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hd⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by simpa only [D, mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hd⟩
    · rintro ⟨⟨x, hx, rfl⟩, hd⟩
      exact ⟨x, ⟨hx, by simpa only [D, mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hd⟩, rfl⟩
  have H (B : Set SectionCoordinates) (hB : MeasurableSet B) :
      mainWallMeasure h B = ∫⁻ y in B ∩ D, ENNReal.ofReal (mainWallChartDensity h y) := by
    rw [mainWallMeasure, withDensity_apply _ hB, Measure.restrict_restrict hB]
  rw [H _ (measurableSet_mainWallReflection_image hA), H _ hA, ← hI]
  have hf (y : SectionCoordinates) : HasFDerivAt mainWallReflection
      mainWallReflectionEquiv.toContinuousLinearMap y := mainWallReflectionEquiv.hasFDerivAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hA.inter hD)
    (fun y _ => (hf y).hasFDerivWithinAt) mainWallReflectionEquiv.injective.injOn]
  have hdet : mainWallReflectionEquiv.toContinuousLinearMap.det = 1 := mainWallReflection_det
  simp only [hdet, abs_one, ENNReal.ofReal_one,
    mainWallChartDensity_reflection, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_mainWallSymmetrization {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    MeasurableSet (mainWallSymmetrization A) := hA.union (measurableSet_mainWallReflection_image hA)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_symmetrization_le {h : ℝ} {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    mainWallMeasure h (mainWallSymmetrization A) ≤ 2 * mainWallMeasure h A := by
  exact (measure_union_le A (mainWallReflection '' A)).trans_eq (by rw [mainWallMeasure_reflection hA, two_mul])

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallReflection_mem_symmetrization_iff {A : Set SectionCoordinates} {y : SectionCoordinates} :
    mainWallReflection y ∈ mainWallSymmetrization A ↔ y ∈ mainWallSymmetrization A := by
  change (mainWallReflection y ∈ A ∨ mainWallReflection y ∈ mainWallReflection '' A) ↔
    (y ∈ A ∨ y ∈ mainWallReflection '' A)
  constructor
  · rintro (h | ⟨z, hz, heq⟩)
    · exact Or.inr ⟨mainWallReflection y, h, mainWallReflection_twice y⟩
    · exact Or.inl ((mainWallReflectionEquiv.injective heq) ▸ hz)
  · rintro (h | ⟨z, hz, rfl⟩)
    · exact Or.inr ⟨y, h, rfl⟩
    · exact Or.inl (by simpa only [mainWallReflection_twice] using hz)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_le_three_volume {h : ℝ} {A : Set SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hA : MeasurableSet A)
    (hsmall : ∀ z ∈ A, |z 0| ≤ 1 / 8 ∧ Real.exp (-z 1) ≤ h / 8 ∧ Real.exp (-z 2) ≤ h / 8) :
    mainWallMeasure h A ≤ ENNReal.ofReal (3 : ℝ) * volume A := by
  rw [mainWallMeasure, withDensity_apply _ hA, Measure.restrict_restrict hA]
  have hAD := hA.inter (isOpen_mainWallChartDomain h).measurableSet
  calc
    _ ≤ ∫⁻ _ in A ∩ mainWallChartDomain h, ENNReal.ofReal (3 : ℝ) := by
      apply setLIntegral_mono' hAD
      intro z hz
      obtain ⟨hs, h₂, h₃⟩ := hsmall z hz.1
      exact ENNReal.ofReal_le_ofReal (small_section_corrected_flux_bounds hh hh1
        (Real.exp_pos _).le (Real.exp_pos _).le h₂ h₃ hs
        (mainWallChart_negative hz.2) (mainWallChart_constraint hz.2)).2.2
    _ = ENNReal.ofReal (3 : ℝ) * volume (A ∩ mainWallChartDomain h) := by simp
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono inter_subset_left)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_three_box {b c : Fin 3 → ℝ} (h : b ≤ c) :
    volume (Icc b c) = ENNReal.ofReal ((c 0 - b 0) * (c 1 - b 1) * (c 2 - b 2)) := by
  rw [Real.volume_Icc_pi]
  simp only [Fin.prod_univ_succ, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
  change ENNReal.ofReal (c 0 - b 0) *
    (ENNReal.ofReal (c 1 - b 1) * ENNReal.ofReal (c 2 - b 2)) = _
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (h 1)), ← ENNReal.ofReal_mul (sub_nonneg.mpr (h 0))]
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnTime_eq {y : ProjectiveState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1} T) : partialCoreReturnTime y = T := hT.csInf_eq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnTime_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnTime =ᶠ[𝓝 y] τ := hτ.mono fun _ h => partialCoreReturnTime_eq h

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnState_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnState =ᶠ[𝓝 y] fun z =>
      let out := projectiveOriginalFlow z 0 (τ z)
      ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hτ, partialCoreReturnTime_eventuallyEq hτ] with z hz ht
  simp only [partialCoreReturnState, ht, toCoreAngleState, hz.1.2.2, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialCurve_annulus {r ρ θ ζ L : ℝ} (hr : 0 < r)
    (hρ : ρ ∈ Icc r (2 * r)) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    ‖restartRadialCurve θ ζ ρ‖ ≤ (2 * (L + 1)) * r ∧
      r / 2 ≤ restartRadialNorm (restartRadialCurve θ ζ ρ) := by
  have hρ0 : 0 < ρ := hr.trans_le hρ.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * (L + 1)) * r)).mpr
    intro i
    fin_cases i
    · change |θ * ρ| ≤ _
      rw [abs_mul, abs_of_pos hρ0]
      have H := mul_le_mul hθ hρ.2 hρ0.le hL
      nlinarith only [H, hr]
    · change |ρ| ≤ _
      rw [abs_of_pos hρ0]
      nlinarith only [hρ.2, mul_nonneg hL hr.le]
    · change |ζ| ≤ _
      rw [abs_of_nonneg hζ.1]
      nlinarith only [hζ.2, hr, mul_nonneg hL hr.le]
  · have hdiff : 0 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg (θ * ρ)) :
      (ρ - ζ) ^ 2 ≤ (θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    rw [Real.sqrt_sq hdiff] at H
    change r / 2 ≤ Real.sqrt ((θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    linarith only [H, hρ.1, hζ.2, hr]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastEntry_control :
    ∃ C ≥ (32 : ℝ), ∀ h ∈ Ioc (0 : ℝ) (1 / (4 * C)),
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let Z := restartRadialCurve θ ζ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
            r ≤ 1 ∧ 8 * (L + 1) * r ≤ 1 / 16 ∧ 0 ≤ T ∧
            0 < restartSectionRadicand h Z ∧ T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * r ^ q ∧ ‖p‖ ≤ 8 * (L + 1) * r ∧ r / 2 ≤ p.2 1 ∧
            (0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ) ∧ p.1 ≤ p.2 1 / 16 ∧ p.2 2 ≤ p.2 1 / 16 ∧
            ‖v‖ ≤ 2 * (L + 1) ∧ |v.1| ≤ 2 * (L + 1) * p.1 / r ∧
            |v.2 2| ≤ 8 * C * (L + 1) * p.2 2 / r := by
  obtain ⟨C, hC, HC⟩ := exists_restartRadialCurve_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, ?_⟩
  intro h hh L hL q hq
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    linarith only [H]
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.1.le]
  let M := 8 * (L + 1)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hL]
  have Hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ((0 < r ∧ r ≤ 1) ∧ M * r ≤ 1 / 16 ∧ C * (M * r) * (q / 2 * Real.log (1 / r)) ≤ 1 / 8) ∧
      r * (q / 2 * Real.log (1 / r)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C (4 * (L + 1)) q,
      eventually_restart_cutoff_budget 1 1 q] with r H₁ H₂
    have heq : 2 * (4 * (L + 1)) * r = M * r := by dsimp only [M]; ring
    rw [heq] at H₁
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨r₀, hr₀, Hr₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min r₀ (1 / 64), lt_min hr₀ (by norm_num), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have Hr := Hr₀ ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrsmall : r ≤ 1 / 64 := hr.2.trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hrsmall, hr.1])⟩
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by linarith only [Hr.1.1.2])))
  obtain ⟨Hcurve, hneg, hnpos, hnexp, hcenter, hactive, hweak, hcv, hnv, hwv⟩ :=
    HC h r T L hh.1 hCh Hr.1.1 hL Hr.1.2.1 hT Hr.1.2.2 Hr.2 θ ζ ρ hθ hζsmall hρ
  change 0 < p.1 at hnpos
  change p.1 ≤ h * Real.exp (-2 * T) at hnexp
  change ‖p.2‖ ≤ M * r at hcenter
  change r / 2 ≤ p.2 1 at hactive
  change 0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ at hweak
  change ∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1) at hcv
  change |v.1| ≤ 2 * (L + 1) * p.1 / r at hnv
  have he : Real.exp (-2 * T) = r ^ q := by
    rw [Real.rpow_def_of_pos hr.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at hnexp
  have hpower : r ^ q ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 Hr.1.1.2 hq.le
  have hnsmall : p.1 ≤ r ^ 2 := hnexp.trans
    ((mul_le_mul_of_nonneg_left hpower hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg r) (by linarith only [hhsmall])))
  have hnr : p.1 ≤ r := hnsmall.trans (by nlinarith only [hr.1, Hr.1.1.2])
  have hp : ‖p‖ ≤ M * r := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos hnpos]
    exact ⟨hnr.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM hr.1.le]), hcenter⟩
  have hv : ‖v‖ ≤ 2 * (L + 1) := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    refine ⟨hnv.trans ?_, (pi_norm_le_iff_of_nonneg (by positivity)).mpr hcv⟩
    apply (div_le_iff₀ hr.1).mpr
    exact mul_le_mul_of_nonneg_left hnr (by positivity)
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζsmall).1
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh.1]) (by
      change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
      have Hb : 8 * (L + 1) * r ≤ 1 / 16 := Hr.1.2.1
      linarith only [hZ, Hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have hcon := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hrad.le) hT).2.1
  refine ⟨Hr.1.1.2, Hr.1.2.1, hT, hrad, hdom, hcon, hneg, Hcurve, hnpos, hnexp, hp,
    hactive, hweak, ?_, ?_, hv, hnv, hwv⟩
  · nlinarith only [hnsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]
  · have Hw := hweak.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))
    nlinarith only [Hw, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmic_wall_window {a P y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hup : Real.exp (-y) ≤ 1) (hlow : a ^ P < Real.exp (-y)) :
    y ∈ Icc 0 (P * |Real.log a|) := by
  have hy0 : 0 ≤ y := by linarith only [Real.exp_le_one_iff.mp hup]
  rw [Real.rpow_def_of_pos ha, Real.exp_lt_exp] at hlow
  refine ⟨hy0, ?_⟩
  rw [abs_of_nonpos (Real.log_nonpos ha.le ha1)]
  nlinarith only [hlow]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_angularUnselectedSection (a L P : ℝ) : MeasurableSet (angularUnselectedSection a L P) := by
  have hρ : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have hmax : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  have hmin : Measurable (fun z : SectionCoordinates => min (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_Icc.preimage hmax).inter
    ((measurableSet_le hρ (measurable_const.mul hmax)).inter (measurableSet_lt measurable_const hmin))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmic_wall_annulus {a y : ℝ} (ha : 0 < a) (hy : Real.exp (-y) ∈ Icc a (2 * a)) :
    y ∈ Icc (-Real.log (2 * a)) (-Real.log a) := by
  have hlow := Real.log_le_log ha hy.1
  have hup := Real.log_le_log (Real.exp_pos (-y)) hy.2
  rw [Real.log_exp] at hlow hup
  constructor <;> linarith only [hlow, hup]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.angularUnselectedSection_subset_boxes {a L P : ℝ}
    (ha : 0 < a) (ha2 : 2 * a ≤ 1) (hL : 0 ≤ L) :
    angularUnselectedSection a L P ⊆ angularLogBox a L P ∪ angularLogBoxSwapped a L P := by
  intro z hz
  have hn₂ : Real.exp (-z 1) ≤ 2 * a := (le_max_left _ _).trans hz.1.2
  have hn₃ : Real.exp (-z 2) ≤ 2 * a := (le_max_right _ _).trans hz.1.2
  have hlow := lt_min_iff.mp hz.2.2
  have ha1 : a ≤ 1 := by linarith only [ha, ha2]
  have hw₂ := logarithmic_wall_window ha ha1 (hn₂.trans ha2) hlow.1
  have hw₃ := logarithmic_wall_window ha ha1 (hn₃.trans ha2) hlow.2
  have hs : |z 0| ≤ 2 * L * a := calc
    _ ≤ _ := hz.2.1
    _ ≤ L * (2 * a) := mul_le_mul_of_nonneg_left hz.1.2 hL
    _ = _ := by ring
  have hs' := abs_le.mp hs
  by_cases ho : Real.exp (-z 2) ≤ Real.exp (-z 1)
  · have hm : Real.exp (-z 1) ∈ Icc a (2 * a) := by simpa only [max_eq_left ho] using hz.1
    have hw := logarithmic_wall_annulus ha hm
    left
    constructor <;> intro i <;> fin_cases i
    · change -2 * L * a ≤ z 0
      linarith only [hs'.1]
    · exact hw.1
    · exact hw₃.1
    · exact hs'.2
    · exact hw.2
    · exact hw₃.2
  · have hm : Real.exp (-z 2) ∈ Icc a (2 * a) := by
      simpa only [max_eq_right (le_of_not_ge ho)] using hz.1
    have hw := logarithmic_wall_annulus ha hm
    right
    constructor <;> intro i <;> fin_cases i
    · change -2 * L * a ≤ z 0
      linarith only [hs'.1]
    · exact hw₂.1
    · exact hw.1
    · exact hs'.2
    · exact hw₂.2
    · exact hw.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_angular_log_boxes {a L P : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hP : 0 ≤ P) :
    volume (angularLogBox a L P) = ENNReal.ofReal (4 * L * P * Real.log 2 * a * |Real.log a|) ∧
    volume (angularLogBoxSwapped a L P) = ENNReal.ofReal (4 * L * P * Real.log 2 * a * |Real.log a|) := by
  have hwidth : -Real.log a - -Real.log (2 * a) = Real.log 2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne']
    ring
  have hlog : -Real.log (2 * a) ≤ -Real.log a := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hLa : 0 ≤ L * a := mul_nonneg hL ha.le
  have hPa : 0 ≤ P * |Real.log a| := mul_nonneg hP (abs_nonneg _)
  constructor
  · have hb : (![-2 * L * a, -Real.log (2 * a), 0] : SectionCoordinates) ≤
        ![2 * L * a, -Real.log a, P * |Real.log a|] := by
      intro i
      fin_cases i
      · change -2 * L * a ≤ 2 * L * a
        nlinarith only [hLa]
      · exact hlog
      · exact hPa
    rw [angularLogBox, volume_three_box hb]
    change ENNReal.ofReal ((2 * L * a - -2 * L * a) * (-Real.log a - -Real.log (2 * a)) *
      (P * |Real.log a| - 0)) = _
    rw [hwidth]
    congr 1
    ring
  · have hb : (![-2 * L * a, 0, -Real.log (2 * a)] : SectionCoordinates) ≤
        ![2 * L * a, P * |Real.log a|, -Real.log a] := by
      intro i
      fin_cases i
      · change -2 * L * a ≤ 2 * L * a
        nlinarith only [hLa]
      · exact hPa
      · exact hlog
    rw [angularLogBoxSwapped, volume_three_box hb]
    change ENNReal.ofReal ((2 * L * a - -2 * L * a) * (P * |Real.log a| - 0) *
      (-Real.log a - -Real.log (2 * a))) = _
    rw [hwidth]
    congr 1
    ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.angularSection_dyadic_cover {d L : ℝ} (hd : 0 < d) :
    angularSection d L = ⋃ j : ℕ, angularSectionAnnulus (dyadicScale d j) L := by
  ext z
  constructor
  · intro hz
    have hm : 0 < max (Real.exp (-z 1)) (Real.exp (-z 2)) := lt_max_of_lt_left (Real.exp_pos _)
    obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd ⟨hm, hz.1⟩
    exact mem_iUnion_of_mem j ⟨hj, hz.2⟩
  · intro hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    have hm : max (Real.exp (-z 1)) (Real.exp (-z 2)) ∈ Ioc 0 d :=
      iUnion_dyadicScale_Ioc hd ▸ mem_iUnion_of_mem j hj.1
    exact ⟨hm.2, hj.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.angularSection_selected_representation {a L P : ℝ} {z : SectionCoordinates}
    (hz : z ∈ angularSectionAnnulus a L) (hn : z ∉ angularUnselectedSection a L P) :
    ∃ θ ζ ρ : ℝ, |θ| ≤ L ∧ (0 < ζ ∧ ζ ≤ a ^ P) ∧ ρ ∈ Icc a (2 * a) ∧
      (z = ![θ * ρ, -Real.log ρ, -Real.log ζ] ∨
        z = mainWallReflection ![θ * ρ, -Real.log ρ, -Real.log ζ]) := by
  have hmin : min (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ a ^ P := by
    by_contra h
    exact hn ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2, lt_of_not_ge h⟩
  by_cases horder : Real.exp (-z 2) ≤ Real.exp (-z 1)
  · have hρ : 0 < Real.exp (-z 1) := Real.exp_pos _
    refine ⟨z 0 / Real.exp (-z 1), Real.exp (-z 2), Real.exp (-z 1), ?_,
      ⟨Real.exp_pos _, by simpa only [min_eq_right horder] using hmin⟩,
      ⟨by simpa only [max_eq_left horder] using hz.1.1.le,
        by simpa only [max_eq_left horder] using hz.1.2⟩, Or.inl ?_⟩
    · rw [abs_div, abs_of_pos hρ]
      exact (div_le_iff₀ hρ).mpr (by simpa only [max_eq_left horder] using hz.2)
    · ext i
      fin_cases i <;> simp [hρ.ne']
  · have horder' := (lt_of_not_ge horder).le
    have hρ : 0 < Real.exp (-z 2) := Real.exp_pos _
    refine ⟨-z 0 / Real.exp (-z 2), Real.exp (-z 1), Real.exp (-z 2), ?_,
      ⟨Real.exp_pos _, by simpa only [min_eq_left horder'] using hmin⟩,
      ⟨by simpa only [max_eq_right horder'] using hz.1.1.le,
        by simpa only [max_eq_right horder'] using hz.1.2⟩, Or.inr ?_⟩
    · rw [abs_div, abs_neg, abs_of_pos hρ]
      exact (div_le_iff₀ hρ).mpr (by simpa only [max_eq_right horder'] using hz.2)
    · ext i
      fin_cases i <;> simp [mainWallReflection, hρ.ne']

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_angularUnselectedSection_le {h a L P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 16)
    (hL : 0 ≤ L) (hLa : 2 * L * a ≤ 1 / 8) (hP : 0 ≤ P) :
    mainWallMeasure h (angularUnselectedSection a L P) ≤
      ENNReal.ofReal (24 * L * P * Real.log 2 * a * |Real.log a|) := by
  have ha2 : 2 * a ≤ 1 := by linarith only [hah, hh1]
  have hsmall (z : SectionCoordinates) (hz : z ∈ angularUnselectedSection a L P) :
      |z 0| ≤ 1 / 8 ∧ Real.exp (-z 1) ≤ h / 8 ∧ Real.exp (-z 2) ≤ h / 8 := by
    have hs : |z 0| ≤ 2 * L * a := calc
      _ ≤ _ := hz.2.1
      _ ≤ L * (2 * a) := mul_le_mul_of_nonneg_left hz.1.2 hL
      _ = _ := by ring
    have hm : max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ h / 8 := by linarith only [hz.1.2, hah]
    exact ⟨hs.trans hLa, (le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩
  have hbox := volume_angular_log_boxes ha hL hP
  have hW : 0 ≤ 4 * L * P * Real.log 2 * a * |Real.log a| :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hP)
      (Real.log_nonneg (by norm_num))) ha.le) (abs_nonneg _)
  calc
    _ ≤ ENNReal.ofReal (3 : ℝ) * volume (angularUnselectedSection a L P) :=
      mainWallMeasure_le_three_volume hh hh1 (measurableSet_angularUnselectedSection a L P) hsmall
    _ ≤ ENNReal.ofReal (3 : ℝ) *
        (volume (angularLogBox a L P) + volume (angularLogBoxSwapped a L P)) :=
      mul_le_mul' le_rfl ((measure_mono (angularUnselectedSection_subset_boxes ha ha2 hL)).trans (measure_union_le _ _))
    _ = _ := by
      rw [hbox.1, hbox.2, ← ENNReal.ofReal_add hW hW, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_angularUnselectedSection_dyadic {h d L P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 16)
    (hL : 0 ≤ L) (hLd : 2 * L * d ≤ 1 / 8) (hP : 0 ≤ P) :
    let E := fun j => angularUnselectedSection (dyadicScale d j) L P
    let C := 24 * L * P * Real.log 2
    MeasurableSet (⋃ j : ℕ, E j) ∧
      (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ := by
  intro E C
  have hd1 : d ≤ 1 := by linarith only [hdh, hh1]
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hP) (Real.log_nonneg (by norm_num))
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤
      ENNReal.ofReal (C * (dyadicScale d j * |Real.log (dyadicScale d j)|)) := by
    have ha := dyadicScale_pos hd j
    have hLa : 2 * L * dyadicScale d j ≤ 1 / 8 :=
      (mul_le_mul_of_nonneg_left (dyadicScale_le hd.le j) (mul_nonneg (by norm_num) hL)).trans hLd
    simpa only [E, C, mul_assoc] using mainWallMeasure_angularUnselectedSection_le hh hh1 ha
      ((dyadicScale_le hd.le j).trans hdh) hL hLa hP
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤
      ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) :=
    (ENNReal.tsum_le_tsum Hlayer).trans_eq (dyadic_log_flux_sum hd hd1 hC)
  have Hunion := (measure_iUnion_le E).trans Hsum
  exact ⟨MeasurableSet.iUnion (fun j => measurableSet_angularUnselectedSection (dyadicScale d j) L P),
    Hsum, Hunion, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReturnParameters_eventuallyEq {h s θ ζ ρ : ℝ} {τ : ProjectiveState → ℝ}
    (hY : ContinuousAt (restartFastProjectiveEntry h s θ ζ) ρ)
    (hτ : ∀ᶠ y in 𝓝 (restartFastProjectiveEntry h s θ ζ ρ), IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) :
    restartReturnParameters h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ a) 0
        (τ (restartFastProjectiveEntry h s θ ζ a))
      coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hY.tendsto.eventually (partialCoreReturnState_eventuallyEq hτ)] with a ha
  exact congrArg coreExitConnectionParameters ha

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartReturn_control :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let y := restartFastProjectiveEntry h s θ ζ ρ
            let p := restartReturnParameters h s θ ζ ρ
            let G := restartReturnState h s θ ζ ρ
            let f := restartReturnPhase h s θ ζ
            let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
            IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreReturnTime y) ∧
              ContDiffAt ℝ 2 partialCoreReturnTime y ∧ connectionReturnValid p ∧
              1 / (2 * (8 * (L + 1) + 1) * r) ≤ G 0 ∧ G 0 ≤ 64 / r ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 4096 * (8 * (L + 1)) * ζ / r ^ 3 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                  (restartReturnTime h s θ ζ ρ))) ∧
              DifferentiableAt ℝ f ρ ∧ |f ρ - F ρ| ≤ C * r ^ 2 ∧
              |deriv f ρ - deriv F ρ| ≤ C * r ∧
              1 / (8 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ C := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartConnection_output_phase
  obtain ⟨hA, hhA, HA⟩ := exists_restartConnection_output_bounds
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hE (min hA hV), lt_min hhE (lt_min hhA hhV), ?_⟩
  intro h hh L hL
  obtain ⟨C, hC, HCE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HCE q P hq hP
  obtain ⟨rA, hrA, HRA⟩ := HA h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rA (min rV 1)), lt_min hrE (lt_min hrA (lt_min hrV (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrA' := hr.2.trans (min_le_right _ _)
  have hrV' := hrA'.trans (min_le_right _ _)
  have hr1 := hrV'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  obtain ⟨_, hY, _⟩ := HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, _, _, hdf, hval, hder, hlo, hhi⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨S, _, hfirstS, hvalid, hradlo, hradhi, hu, hw, hsum, horbit⟩ :=
    HRA r ⟨hr.1, hrA'.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hvalid hradlo hradhi hu hw hsum horbit
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  have heqTime := partialCoreReturnTime_eventuallyEq hnear
  have ht : partialCoreReturnTime (Y ρ) = T := heqTime.self_of_nhds.trans hτ
  have hp : restartReturnParameters h s θ ζ ρ =
      coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T)) := by
    change coreExitConnectionParameters (toCoreAngleState
      (projectiveOriginalFlow (Y ρ) 0 (partialCoreReturnTime (Y ρ)))) = _
    rw [ht]
  have hg : restartReturnState h s θ ζ ρ =
      connectionReturnPhysicalState (coreExitConnectionParameters
        (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T))) := congrArg connectionReturnPhysicalState hp
  have heq := restartReturnParameters_eventuallyEq hY.continuousAt hnear
  have heqPhase : restartReturnPhase h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (Y a) 0 (τ (Y a))
      2 / connectionReturnPhysicalState
        (coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3]) 0 :=
    heq.mono fun _ ha => congrArg (fun p => 2 / connectionReturnPhysicalState p 0) ha
  dsimp only [s, Y] at ht hp hg heqPhase
  refine ⟨?_, hcτ.congr_of_eventuallyEq heqTime, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hdf.congr_of_eventuallyEq heqPhase, ?_, ?_, ?_, ?_⟩
  · simpa only [ht] using hfirst
  · simpa only [hp] using hvalid
  · simpa only [hg] using hradlo
  · simpa only [hg] using hradhi
  · simpa only [hg] using hu
  · simpa only [hg] using hw
  · simpa only [hg] using hsum
  · simpa only [restartReturnTime, ht, hp, hg] using horbit
  · simpa only [heqPhase.self_of_nhds] using hval
  · simpa only [heqPhase.deriv_eq] using hder
  · simpa only [heqPhase.deriv_eq] using hlo
  · simpa only [heqPhase.deriv_eq] using hhi

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChart_restartRadial {h θ ζ ρ : ℝ} (hρ : 0 < ρ) (hζ : 0 < ζ) :
    mainWallChart h ![θ * ρ, -Real.log ρ, -Real.log ζ] =
      restartSectionChart h (restartRadialCurve θ ζ ρ) := by
  simp [mainWallChart, mainWallRadicand, restartSectionChart, restartSectionRadicand,
    restartRadialCurve, Real.exp_log hρ, Real.exp_log hζ]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartReturn_reflected_orbit :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ a ^ P) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let y : SectionCoordinates := ![θ * ρ, -Real.log ρ, -Real.log ζ]
          let T := restartReturnTime h s θ ζ ρ
          let G := restartReturnState h s θ ζ ρ
          y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
            coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)) ∧
            coreRadiusEntry G = toProjectiveState (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartReturn_control
  obtain ⟨C, hC32, HV⟩ := exists_restartFastEntry_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC32
  refine ⟨min hC (1 / (4 * C)), lt_min hhC (by positivity), ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨K, _, HK⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨aC, haC, HaC⟩ := HK q P hq hP
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q (by linarith)
  refine ⟨min aC (min aV 1), lt_min haC (lt_min haV zero_lt_one), ?_⟩
  intro a ha θ ζ hθ hζ ρ hρ s y T G
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ a ^ 2 := ⟨hζ.1.le, hζ.2.trans (by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 (by linarith : (2 : ℝ) ≤ P))⟩
  obtain ⟨_, _, hs, hrad, _⟩ := HaV a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨hfirst, _, hvalid, _, _, _, _, _, horbit, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  have heq : mainWallChart h y = restartSectionChart h (restartRadialCurve θ ζ ρ) :=
    mainWallChart_restartRadial (ha.1.trans_le hρ.1) hζ.1
  have hy : y ∈ mainWallChartDomain h := by
    change 0 < mainWallRadicand h y
    change 0 < 1 - (θ * ρ) ^ 2 - curvature h ρ ζ at hrad
    simpa [y, mainWallRadicand, Real.exp_log (ha.1.trans_le hρ.1), Real.exp_log hζ.1] using hrad
  have ht : 0 < T := add_pos (add_pos_of_nonneg_of_pos hs hfirst.1.1) hvalid.1.1.1
  have hdom : T ∈ normalizedMaxDomain (mainWallChart h y) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint (mainWallChart_constraint hy) 0 ht.le
  have ho : coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)) := by
    simpa only [heq] using horbit
  refine ⟨hy, ht, hdom, ho, ?_⟩
  rw [normalizedMaxCurve_mainWallReflection hdom, toProjectiveState_axisSwap]
  exact ho

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartLabelSet (L r P : ℝ) : MeasurableSet (restartLabelSet L r P) :=
  (measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.era_radial_good_iff {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ}
    {Y : CoreAngleState} {x : ℝ} (hx : x ∈ Ioo 0 1) (hmatch : Γ.state (2 / x) = Y) :
    x ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap ↔ (B, Y) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
  change (x ∈ Ioo 0 1 ∧ (B, Γ.state (2 / x)) ∈ EraSurvivor.typicalDomain η J σ Bcap) ↔ _
  rw [hmatch]
  exact and_iff_right hx

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.era_radial_failure_weighted {Γ : EraCurve} {η σ B Bcap a b c : ℝ} {J : ℕ}
    {Y : ℝ → CoreAngleState} {f : ℝ → ℝ} (hc : 0 < c)
    (hf : ∀ ρ ∈ Icc a b, DifferentiableAt ℝ f ρ) (hder : ∀ ρ ∈ Icc a b, c ≤ deriv f ρ)
    (hunit : ∀ ρ ∈ Icc a b, f ρ ∈ Ioo 0 1)
    (hmatch : ∀ ρ ∈ Icc a b, Γ.state (2 / f ρ) = Y ρ)
    (hG : MeasurableSet (EraSurvivor.curveTypicalSet Γ η J σ B Bcap))
    (hloss : volume (Ioo 0 1 \ EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ≤ ENNReal.ofReal (80 * B ^ σ)) :
    MeasurableSet (eraRadialFailure η J σ B Bcap a b Y) ∧
      ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc a b → ∀ (ω : ℝ → ℝ≥0∞) (M : ℝ), 0 ≤ M →
        (∀ ρ ∈ A, ω ρ ≤ ENNReal.ofReal M) →
        (∫⁻ ρ in A ∩ eraRadialFailure η J σ B Bcap a b Y, ω ρ) ≤
          min (∫⁻ ρ in A, ω ρ) (ENNReal.ofReal (M / c) * ENNReal.ofReal (80 * B ^ σ)) := by
  let G := EraSurvivor.curveTypicalSet Γ η J σ B Bcap
  have heq : eraRadialFailure η J σ B Bcap a b Y = Icc a b \ f ⁻¹' G := by
    ext ρ
    change (ρ ∈ Icc a b ∧ (B, Y ρ) ∉ EraSurvivor.typicalDomain η J σ Bcap) ↔ (ρ ∈ Icc a b ∧ f ρ ∉ G)
    exact and_congr_right (fun hρ => not_congr (era_radial_good_iff (hunit ρ hρ) (hmatch ρ hρ)).symm)
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact measurableSet_radial_failure (fun ρ hρ => (hf ρ hρ).continuousAt.continuousWithinAt)
      measurableSet_Icc Subset.rfl hG
  · intro A hA hAI ω M hM hω
    have hrestrict : A ∩ eraRadialFailure η J σ B Bcap a b Y = A \ f ⁻¹' G := by
      rw [heq]
      ext ρ
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hAI h.1, h.2⟩⟩
    rw [hrestrict]
    exact (radial_phase_failure_weighted hc hM hf hder hA hAI
      (fun ρ hρ => hunit ρ (hAI hρ)) hG hloss hω).2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.statisticalCoreFuture_of_entry_or_reflection {η σ Bcap T : ℝ} {J : ℕ}
    {x : NormalizedState} {p : eraSurvivorDomain η J σ Bcap}
    (ht : 0 < T) (hdom : T ∈ normalizedMaxDomain x 0)
    (hstat : EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p))
    (ho : coreRadiusEntry p.val.2 = toProjectiveState (normalizedMaxCurve x 0 T) ∨
      coreRadiusEntry p.val.2 = projectiveReflection (toProjectiveState (normalizedMaxCurve x 0 T))) :
    StatisticalCoreFuture η J σ Bcap x := by
  rcases ho with ho | ho
  · exact ⟨T, ht, hdom, 0, p, hstat, ho⟩
  · refine ⟨T, ht, hdom, 3, p, hstat, ?_⟩
    change coreRadiusEntry p.val.2 = toProjectiveState (axisSwap (normalizedMaxCurve x 0 T))
    rw [toProjectiveState_axisSwap]
    exact ho

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restart_era_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ rstar > (0 : ℝ),
              ∀ r ∈ Ioc (0 : ℝ) rstar,
                let s := q / 2 * Real.log (1 / r)
                MeasurableSet {p : restartLabelSet L r P × Icc r (2 * r) |
                  (p.2 : ℝ) ∈ eraRadialFailure η J σ (restartAmplitudeBudget L r p.1.val.2) Bcap r (2 * r)
                    (restartReturnState h s p.1.val.1 p.1.val.2)} ∧
                ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
                  let B := restartAmplitudeBudget L r ζ
                  let Y := restartReturnState h s θ ζ
                  let F := eraRadialFailure η J σ B Bcap r (2 * r) Y
                  B ∈ Ioc 0 Bcap ∧ MeasurableSet F ∧
                    (∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc r (2 * r) →
                      ∀ (ω : ℝ → ℝ≥0∞) (M : ℝ), 0 ≤ M → (∀ ρ ∈ A, ω ρ ≤ ENNReal.ofReal M) →
                        (∫⁻ ρ in A ∩ F, ω ρ) ≤ min (∫⁻ ρ in A, ω ρ)
                          (ENNReal.ofReal (640 * Real.sqrt 3 * M * B ^ σ))) ∧
                    ∀ ρ ∈ Icc r (2 * r), ρ ∉ F →
                      ∃ p : eraSurvivorDomain η J σ Bcap, p.val = (B, Y ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_joint_statistics hBirkhoff
  obtain ⟨hstar, hhstar, HP⟩ := exists_restart_statistical_preparation
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, htyp, Bs, hBs, hBscap, Hstats⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HP h hh L hL q P hq hP Bs hBs
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr s
  obtain ⟨hY, Hcurve⟩ := HR r hr
  refine ⟨?_, ?_⟩
  · have hbad := htyp.compl.preimage hY
    convert! hbad using 1
    ext p
    change ((p.2 : ℝ) ∈ Icc r (2 * r) ∧
      (restartAmplitudeBudget L r p.1.val.2, restartReturnState h s p.1.val.1 p.1.val.2 p.2) ∉
        EraSurvivor.typicalDomain η J σ Bcap) ↔ _
    exact and_iff_right p.2.property
  · intro θ ζ hθ hζ B Y F
    obtain ⟨hB, hΓ, Hradial⟩ := Hcurve θ ζ hθ hζ
    let Γ := restartEraCurve h s θ ζ r
    let f := restartReturnPhase h s θ ζ
    obtain ⟨hG, _, Hloss, Hgood⟩ := Hstats B hB Γ hΓ
    have hloss : volume (Ioo 0 1 \ EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ≤ ENNReal.ofReal (80 * B ^ σ) := by
      simpa only [univ_inter] using (Hloss univ).trans (min_le_right _ _)
    have Hfail := era_radial_failure_weighted (Γ := Γ) (Y := Y) (f := f)
      (by positivity : 0 < 1 / (8 * Real.sqrt (3 : ℝ)))
      (fun ρ hρ => (Hradial ρ hρ).2.1) (fun ρ hρ => (Hradial ρ hρ).2.2.1)
      (fun ρ hρ => (Hradial ρ hρ).1) (fun ρ hρ => (Hradial ρ hρ).2.2.2) hG hloss
    refine ⟨⟨hB.1, hB.2.trans hBscap⟩, Hfail.1, ?_, ?_⟩
    · intro A hA hAI ω M hM hω
      have H := Hfail.2 A hA hAI ω M hM hω
      have hcoef : ENNReal.ofReal (M / (1 / (8 * Real.sqrt 3))) * ENNReal.ofReal (80 * B ^ σ) =
          ENNReal.ofReal (640 * Real.sqrt 3 * M * B ^ σ) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ M / (1 / (8 * Real.sqrt 3)))]
        congr 1
        simp only [one_div, div_inv_eq_mul]
        ring
      simpa only [hcoef] using H
    · intro ρ hρ hnot
      have hgood : (B, Y ρ) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
        by_contra hn
        exact hnot ⟨hρ, hn⟩
      have hfgood : f ρ ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap :=
        (era_radial_good_iff (Hradial ρ hρ).1 (Hradial ρ hρ).2.2.2).mpr hgood
      obtain ⟨p, hp, hstat⟩ := Hgood (f ρ) hfgood
      exact ⟨p, hp.trans (congrArg (fun Z => (B, Z)) (Hradial ρ hρ).2.2.2), hstat⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.angularFailureFluxConstant_ge_one {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ) :
    1 ≤ angularFailureFluxConstant L σ := by
  have hp : 1 ≤ (102400 * (L + 1)) ^ σ := Real.one_le_rpow (by linarith) hσ
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have H := mul_le_mul hs hp (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)
  dsimp only [angularFailureFluxConstant]
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartAmplitudeBudget_normalized {L a t σ : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (ht : 0 ≤ t) :
    640 * Real.sqrt 3 * (restartAmplitudeBudget L a (2 * a * t)) ^ σ =
      (angularFailureFluxConstant L σ * a ^ (-2 * σ)) * t ^ σ := by
  have hB : restartAmplitudeBudget L a (2 * a * t) = (102400 * (L + 1)) * (a ^ (-2 : ℝ) * t) := by
    rw [Real.rpow_neg ha.le, Real.rpow_two]
    unfold restartAmplitudeBudget
    field_simp
    ring
  rw [hB, Real.mul_rpow (by positivity) (mul_nonneg (Real.rpow_nonneg ha.le _) ht),
    Real.mul_rpow (Real.rpow_nonneg ha.le _) ht, ← Real.rpow_mul ha.le]
  dsimp only [angularFailureFluxConstant]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_restartAngularFailureCoordinates {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (hjoint : MeasurableSet {p : restartLabelSet L a P × Icc a (2 * a) |
      (p.2 : ℝ) ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a p.1.val.2) Bcap a (2 * a)
        (restartReturnState h s p.1.val.1 p.1.val.2)}) :
    MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap) := by
  let D : Set SectionCoordinates := {z | (z 1, 2 * a * z 2) ∈ restartLabelSet L a P ∧ z 0 ∈ Icc a (2 * a)}
  have hD : MeasurableSet D :=
    ((measurableSet_restartLabelSet L a P).preimage (by fun_prop)).inter
      (measurableSet_Icc.preimage (measurable_pi_apply 0))
  let g : D → restartLabelSet L a P × Icc a (2 * a) := fun z =>
    (⟨(z.val 1, 2 * a * z.val 2), z.property.1⟩, ⟨z.val 0, z.property.2⟩)
  have hg : Measurable g := by
    apply Measurable.prodMk
    · apply Measurable.subtype_mk
      exact ((measurable_pi_apply 1).comp measurable_subtype_coe).prodMk
        (measurable_const.mul ((measurable_pi_apply 2).comp measurable_subtype_coe))
    · exact ((measurable_pi_apply 0).comp measurable_subtype_coe).subtype_mk
  have H := hD.subtype_image (hjoint.preimage hg)
  have heq : Subtype.val '' g ⁻¹' {p : restartLabelSet L a P × Icc a (2 * a) |
      (p.2 : ℝ) ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a p.1.val.2) Bcap a (2 * a)
        (restartReturnState h s p.1.val.1 p.1.val.2)} =
      {z : SectionCoordinates | (z 1, 2 * a * z 2) ∈ restartLabelSet L a P ∧
        z 0 ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a (2 * a * z 2)) Bcap a (2 * a)
          (restartReturnState h s (z 1) (2 * a * z 2))} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property.1, hw⟩
    · intro hz
      exact ⟨⟨z, hz.1, hz.2.1⟩, hz.2, rfl⟩
  rw [heq] at H
  exact (measurableSet_Icc.preimage (measurable_pi_apply 1)).inter
    ((measurableSet_Ioo.preimage (measurable_pi_apply 2)).inter H)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_restartAngularFailureSection {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (ha : 0 < a) (hA : MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap)) :
    MeasurableSet (restartAngularFailureSection h s a L P η J σ Bcap) := by
  have hpos (z : SectionCoordinates) (hz : z ∈ restartAngularFailureCoordinates h s a L P η J σ Bcap) :
      0 < z 0 ∧ 0 < z 2 := ⟨ha.trans_le hz.2.2.2.1.1, hz.2.1.1⟩
  exact hA.image_of_continuousOn_injOn
    (fun z hz => (hasFDerivAt_scaledAngularLogCoordinates ha (hpos z hz).1 (hpos z hz).2).continuousAt.continuousWithinAt)
    ((scaledAngularLogCoordinates_injOn ha).mono hpos)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mem_restartAngularFailureSection_iff {h s a L P η σ Bcap θ ζ ρ : ℝ} {J : ℕ}
    (ha : 0 < a) (hθ : |θ| ≤ L) (hζ : 0 < ζ ∧ ζ < 2 * a) (hl : ζ ≤ a ^ P) (hρ : 0 < ρ) :
    ![θ * ρ, -Real.log ρ, -Real.log ζ] ∈ restartAngularFailureSection h s a L P η J σ Bcap ↔
      ρ ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ) := by
  let z : SectionCoordinates := ![ρ, θ, ζ / (2 * a)]
  have ht : ζ / (2 * a) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hζ.1 (by positivity), (div_lt_one (by positivity)).mpr hζ.2⟩
  have heq : 2 * a * (ζ / (2 * a)) = ζ := mul_div_cancel₀ _ (by positivity)
  have hmap : scaledAngularLogCoordinates a z = ![θ * ρ, -Real.log ρ, -Real.log ζ] := by
    simp [scaledAngularLogCoordinates, z, heq]
  have hmember : z ∈ restartAngularFailureCoordinates h s a L P η J σ Bcap ↔
      ρ ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ) := by
    simp [restartAngularFailureCoordinates, z, heq, ht.1, ht.2, restartLabelSet, hθ, hl, hζ.1,
      (abs_le.mp hθ).1, (abs_le.mp hθ).2]
  rw [← hmap, ← hmember]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwpos : 0 < w 0 ∧ 0 < w 2 := ⟨ha.trans_le hw.2.2.2.1.1, hw.2.1.1⟩
    exact (scaledAngularLogCoordinates_injOn ha hwpos ⟨hρ, ht.1⟩ hwz) ▸ hw
  · exact fun hz => ⟨z, hz, rfl⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.volume_restartAngularFailureSection_le {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (ha : 0 < a) (hL : 0 ≤ L)
    (hA : MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap))
    (Hslice : ∀ θ ζ : ℝ, (θ, ζ) ∈ restartLabelSet L a P →
      volume (eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ)) ≤ ENNReal.ofReal (min a (640 * Real.sqrt 3 * (restartAmplitudeBudget L a ζ) ^ σ))) :
    volume (restartAngularFailureSection h s a L P η J σ Bcap) ≤
      ENNReal.ofReal (2 * L) * logarithmicLayerCostOne a (angularFailureFluxConstant L σ) σ := by
  let A := restartAngularFailureCoordinates h s a L P η J σ Bcap
  let f : SectionCoordinates → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / z 2)
  have hf : Measurable f := (measurable_const.div (measurable_pi_apply 2)).ennreal_ofReal
  rw [restartAngularFailureSection, volume_scaledAngularLogCoordinates ha hA
    (fun z hz => ⟨ha.trans_le hz.2.2.2.1.1, hz.2.1.1⟩)]
  change (∫⁻ z in A, f z) ≤ _
  rw [← lintegral_indicator hA, lintegral_three_coordinates (hf.indicator hA)]
  calc
    _ ≤ ∫⁻ θ in Icc (-L) L, ∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (min a ((angularFailureFluxConstant L σ * a ^ (-2 * σ)) * t ^ σ) / t) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_mono
      intro θ
      by_cases hθ : -L ≤ θ ∧ θ ≤ L
      · rw [indicator_of_mem (show θ ∈ Icc (-L) L from hθ), ← lintegral_indicator measurableSet_Ioo]
        apply lintegral_mono
        intro t
        by_cases ht : 0 < t ∧ t < 1
        · rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ht)]
          by_cases hl : (θ, 2 * a * t) ∈ restartLabelSet L a P
          · let F := eraRadialFailure η J σ (restartAmplitudeBudget L a (2 * a * t)) Bcap a (2 * a)
              (restartReturnState h s θ (2 * a * t))
            have hF : MeasurableSet F := by
              have H := hA.preimage (show Measurable (fun r : ℝ => ![r, θ, t]) by fun_prop)
              simpa [restartAngularFailureCoordinates, hθ, ht, hl, F] using H
            have heq : (fun r => A.indicator f ![r, θ, t]) = F.indicator (fun _ => ENNReal.ofReal (1 / t)) := by
              funext r
              simp [indicator, A, restartAngularFailureCoordinates, f, F, hθ, ht, hl]
            change (∫⁻ r, A.indicator f ![r, θ, t]) ≤ _
            rw [heq, lintegral_indicator hF, lintegral_const, Measure.restrict_apply_univ]
            calc
              _ ≤ ENNReal.ofReal (1 / t) * ENNReal.ofReal (min a (640 * Real.sqrt 3 *
                  (restartAmplitudeBudget L a (2 * a * t)) ^ σ)) := mul_le_mul' le_rfl (Hslice θ (2 * a * t) hl)
              _ = _ := by
                rw [restartAmplitudeBudget_normalized hL ha ht.1.le,
                  ← ENNReal.ofReal_mul (one_div_nonneg.mpr ht.1.le)]
                congr 1
                ring
          · simp [indicator, restartAngularFailureCoordinates, hl]
        · simp [indicator, restartAngularFailureCoordinates, ht]
      · simp [indicator, restartAngularFailureCoordinates, hθ]
    _ = _ := by
      change (∫⁻ _ in Icc (-L) L, logarithmicLayerCostOne a (angularFailureFluxConstant L σ) σ) = _
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        show L - -L = 2 * L by ring, mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.mainWallMeasure_restartAngularFailureSection_le_volume {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 16)
    (hL : 0 ≤ L) (hLa : 2 * L * a ≤ 1 / 8)
    (hA : MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap)) :
    mainWallMeasure h (restartAngularFailureSection h s a L P η J σ Bcap) ≤
      ENNReal.ofReal (3 : ℝ) * volume (restartAngularFailureSection h s a L P η J σ Bcap) := by
  apply mainWallMeasure_le_three_volume hh hh1 (measurableSet_restartAngularFailureSection ha hA)
  rintro _ ⟨z, hz, rfl⟩
  have hρ : 0 < z 0 := ha.trans_le hz.2.2.2.1.1
  have ht : 0 < 2 * a * z 2 := mul_pos (by positivity) hz.2.1.1
  have hsmall : 2 * a ≤ h / 8 := by linarith only [hah]
  have hθ : |z 1| ≤ L := abs_le.mpr hz.1
  have hs : |z 1 * z 0| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_pos hρ]
    have H := mul_le_mul hθ hz.2.2.2.1.2 hρ.le hL
    nlinarith only [H, hLa]
  change |z 1 * z 0| ≤ 1 / 8 ∧ Real.exp (- -Real.log (z 0)) ≤ h / 8 ∧
    Real.exp (- -Real.log (2 * a * z 2)) ≤ h / 8
  rw [neg_neg, neg_neg, Real.exp_log hρ, Real.exp_log ht]
  exact ⟨hs, hz.2.2.2.1.2.trans hsmall,
    (mul_le_of_le_one_right (by positivity : 0 ≤ 2 * a) hz.2.1.2.le).trans hsmall⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restartAngular_physical_failure (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
              ∀ a ∈ Ioc (0 : ℝ) astar,
                let s := q / 2 * Real.log (1 / a)
                let E := restartAngularFailureSection h s a L P η J σ Bcap
                let K := 6 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
                MeasurableSet E ∧ mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) ∧
                  mainWallMeasure h E ≠ ⊤ ∧
                  ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ a ^ P) →
                    ∀ ρ ∈ Icc a (2 * a), ![θ * ρ, -Real.log ρ, -Real.log ζ] ∉ E →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartAmplitudeBudget L a ζ, restartReturnState h s θ ζ ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restart_era_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh L hL q P hq hP
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  refine ⟨min aS (min (h / 16) (1 / (16 * (L + 1)))),
    lt_min haS (lt_min (div_pos hh.1 (by norm_num)) (by positivity)), ?_⟩
  intro a ha s E K
  have hah : a ≤ h / 16 := ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 := by linarith only [hah, hh1]
  have hLa : 2 * L * a ≤ 1 / 8 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * (L + 1))).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [H, ha.1]
  obtain ⟨hjoint, Hstats⟩ := HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
  have hA := measurableSet_restartAngularFailureCoordinates hjoint
  have Hslice (θ ζ : ℝ) (hl : (θ, ζ) ∈ restartLabelSet L a P) :
      volume (eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ)) ≤ ENNReal.ofReal (min a (640 * Real.sqrt 3 * (restartAmplitudeBudget L a ζ) ^ σ)) := by
    let F := eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a) (restartReturnState h s θ ζ)
    have hFI : F ⊆ Icc a (2 * a) := fun _ hρ => hρ.1
    have H := (Hstats θ ζ hl.1 hl.2).2.2.1 (Icc a (2 * a)) measurableSet_Icc (Subset.refl _)
      (fun _ => (1 : ℝ≥0∞)) 1 (by norm_num) (by intros; norm_num)
    change (∫⁻ _ in Icc a (2 * a) ∩ F, (1 : ℝ≥0∞)) ≤ _ at H
    rw [inter_eq_right.mpr hFI] at H
    simpa only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc,
      show 2 * a - a = a by ring, mul_one, ← ENNReal.ofReal_min] using H
  have Hbound : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) := calc
    _ ≤ _ := mainWallMeasure_restartAngularFailureSection_le_volume hh.1 hh1 ha.1 hah hL hLa hA
    _ ≤ ENNReal.ofReal (3 : ℝ) *
        (ENNReal.ofReal (2 * L) * logarithmicLayerCostOne a (angularFailureFluxConstant L σ) σ) :=
      mul_le_mul' le_rfl (volume_restartAngularFailureSection_le ha.1 hL hA Hslice)
    _ ≤ ENNReal.ofReal (3 : ℝ) * (ENNReal.ofReal (2 * L) * ENNReal.ofReal
        (logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ * a * (1 + |Real.log a|))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (logarithmicLayerCostOne_le ha.1 ha1
        (angularFailureFluxConstant_ge_one hL hσ.le) hσ))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * L), ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_restartAngularFailureSection ha.1 hA, Hbound,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro θ ζ hθ hζ ρ hρ hn
  have hζa : ζ < 2 * a := (hζ.2.trans (Real.rpow_le_self_of_le_one ha.1.le ha1 (by linarith))).trans_lt (by linarith only [ha.1])
  exact (Hstats θ ζ hθ hζ).2.2.2 ρ hρ (fun hbad => hn
    ((mem_restartAngularFailureSection_iff ha.1 hθ ⟨hζ.1, hζa⟩ hζ.2 (ha.1.trans_le hρ.1)).mpr hbad))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restartAngular_two_orders (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
              ∀ a ∈ Ioc (0 : ℝ) astar,
                let s := q / 2 * Real.log (1 / a)
                let E := mainWallSymmetrization (restartAngularFailureSection h s a L P η J σ Bcap)
                let K := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
                MeasurableSet E ∧ mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) ∧
                  mainWallMeasure h E ≠ ⊤ ∧
                  ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ a ^ P) → ∀ ρ ∈ Icc a (2 * a),
                    let y : SectionCoordinates := ![θ * ρ, -Real.log ρ, -Real.log ζ]
                    let T := restartReturnTime h s θ ζ ρ
                    y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
                      ((y ∉ E ∨ mainWallReflection y ∉ E) →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartAmplitudeBudget L a ζ, restartReturnState h s θ ζ ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) ∧
                        coreRadiusEntry p.val.2 = projectiveReflection (toProjectiveState
                          (normalizedMaxCurve (mainWallChart h y) 0 T)) ∧
                        coreRadiusEntry p.val.2 = toProjectiveState
                          (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_physical_failure hBirkhoff
  obtain ⟨hO, hhO, HO⟩ := exists_restartReturn_reflected_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS hO, lt_min hhS hhO, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨aO, haO, HaO⟩ := HO h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
  refine ⟨min aS aO, lt_min haS haO, ?_⟩
  intro a ha s E K
  obtain ⟨hF, hbound, _, Hgood⟩ := HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
  have HE : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) := calc
    _ ≤ _ := mainWallMeasure_symmetrization_le hF
    _ ≤ 2 * ENNReal.ofReal ((6 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ) * a * (1 + |Real.log a|)) :=
      mul_le_mul' le_rfl hbound
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_mainWallSymmetrization hF, HE, ne_top_of_le_ne_top ENNReal.ofReal_ne_top HE, ?_⟩
  intro θ ζ hθ hζ ρ hρ y T
  obtain ⟨hy, ht, hdom, ho, hos⟩ := HaO a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  refine ⟨hy, ht, hdom, ?_⟩
  intro H
  have hn : y ∉ E := H.elim id (fun hs hy => hs (mainWallReflection_mem_symmetrization_iff.mpr hy))
  obtain ⟨p, hp, hstat⟩ := Hgood θ ζ hθ hζ ρ hρ (fun hbad => hn (Or.inl hbad))
  exact ⟨p, hp, hstat, by simpa only [hp] using ho, by simpa only [hp] using hos⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restartAngular_two_orders_dyadic (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ dstar > (0 : ℝ),
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let E := fun j => mainWallSymmetrization (restartAngularFailureSection h
                  (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) L P η J σ Bcap)
                let K := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
                (∀ j : ℕ, MeasurableSet (E j)) ∧ MeasurableSet (⋃ j : ℕ, E j) ∧
                  (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ ∧
                  ∀ j : ℕ, ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ (dyadicScale d j) ^ P) →
                    ∀ ρ ∈ Icc (dyadicScale d j) (2 * dyadicScale d j),
                      let s := q / 2 * Real.log (1 / dyadicScale d j)
                      let y : SectionCoordinates := ![θ * ρ, -Real.log ρ, -Real.log ζ]
                      let T := restartReturnTime h s θ ζ ρ
                      y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
                        ((y ∉ ⋃ i : ℕ, E i ∨ mainWallReflection y ∉ ⋃ i : ℕ, E i) →
                        ∃ p : eraSurvivorDomain η J σ Bcap,
                          p.val = (restartAmplitudeBudget L (dyadicScale d j) ζ, restartReturnState h s θ ζ ρ) ∧
                          EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) ∧
                          coreRadiusEntry p.val.2 = projectiveReflection (toProjectiveState
                            (normalizedMaxCurve (mainWallChart h y) 0 T)) ∧
                          coreRadiusEntry p.val.2 = toProjectiveState
                            (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_two_orders hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh L hL q P hq hP
  refine ⟨min astar 1, lt_min hastar zero_lt_one, ?_⟩
  intro d hd E K
  have Hdata (j : ℕ) := Ha (dyadicScale d j)
    ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩
  have hE (j : ℕ) : MeasurableSet (E j) := (Hdata j).1
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hL)
    (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one hL hσ.le) hσ)
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤ ENNReal.ofReal
      (K * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|))) := by
    simpa only [E, K, mul_assoc] using (Hdata j).2.1
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤
      ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) :=
    (ENNReal.tsum_le_tsum Hlayer).trans_eq (dyadic_log_one_flux_sum hd.1 (hd.2.trans (min_le_right _ _)) hK)
  have Hunion := (measure_iUnion_le E).trans Hsum
  refine ⟨hE, MeasurableSet.iUnion hE, Hsum, Hunion,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion, ?_⟩
  intro j θ ζ hθ hζ ρ hρ s y T
  obtain ⟨hy, ht, hdom, Hgood⟩ := (Hdata j).2.2.2 θ ζ hθ hζ ρ hρ
  refine ⟨hy, ht, hdom, ?_⟩
  intro H
  apply Hgood
  exact H.imp (fun hn hbad => hn (mem_iUnion_of_mem j hbad))
    (fun hn hbad => hn (mem_iUnion_of_mem j hbad))

end
end

/-- Outside one finite-flux Borel set, every point of the full bounded-angle section reaches a statistical core on its exact orbit. -/
theorem solution (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ dstar > (0 : ℝ),
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := angularFailureRegion h q d L P η J σ Bcap
                let C := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ +
                  24 * L * P * Real.log 2
                MeasurableSet F ∧ mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h F ≠ ⊤ ∧
                  ∀ z ∈ angularSection d L \ F,
                    z ∈ mainWallChartDomain h ∧ StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_two_orders_dyadic hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  refine ⟨min dS (min (h / 16) (1 / (16 * (L + 1)))),
    lt_min hdS (lt_min (div_pos hh.1 (by norm_num)) (by positivity)), ?_⟩
  intro d hd F C
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  have hdh : d ≤ h / 16 := hd.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hLd : 2 * L * d ≤ 1 / 8 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * (L + 1))).mp
      (hd.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [H, hd.1]
  let S := ⋃ j : ℕ, mainWallSymmetrization (restartAngularFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) L P η J σ Bcap)
  let U := ⋃ j : ℕ, angularUnselectedSection (dyadicScale d j) L P
  let K := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
  let A := 24 * L * P * Real.log 2
  obtain ⟨_, hS, _, HSbound, _, Hgood⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  obtain ⟨hU, _, HUbound, _⟩ := mainWallMeasure_angularUnselectedSection_dyadic hh.1 hh1 hd.1 hdh hL hLd (by linarith : 0 ≤ P)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hL)
    (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one hL hσ.le) hσ)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (by linarith)) hlog
  have hW : 0 ≤ 1 + |Real.log d| + 2 * Real.log 2 := by positivity
  have HU' : mainWallMeasure h U ≤ ENNReal.ofReal (A * d * (1 + |Real.log d| + 2 * Real.log 2)) :=
    HUbound.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hd.1.le)))
  have Hbound : mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d| + 2 * Real.log 2)) := calc
    _ ≤ mainWallMeasure h S + mainWallMeasure h U := measure_union_le S U
    _ ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) +
        ENNReal.ofReal (A * d * (1 + |Real.log d| + 2 * Real.log 2)) := add_le_add HSbound HU'
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hK hd.1.le) hW)
        (mul_nonneg (mul_nonneg hA hd.1.le) hW)]
      congr 1
      change K * d * _ + A * d * _ = (K + A) * d * _
      ring
  refine ⟨hS.union hU, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro z hz
  have hcover : z ∈ ⋃ j : ℕ, angularSectionAnnulus (dyadicScale d j) L := by
    rw [← angularSection_dyadic_cover hd.1]
    exact hz.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
  have hzS : z ∉ S := fun hbad => hz.2 (Or.inl hbad)
  have hzU : z ∉ angularUnselectedSection (dyadicScale d j) L P :=
    fun hbad => hz.2 (Or.inr (mem_iUnion_of_mem j hbad))
  obtain ⟨θ, ζ, ρ, hθ, hζ, hρ, hzcoord⟩ := angularSection_selected_representation hj hzU
  obtain ⟨hy, ht, hdom, Hstats⟩ := Hgood j θ ζ hθ hζ ρ hρ
  rcases hzcoord with heq | heq
  · subst z
    obtain ⟨p, _, hstat, horbit, _⟩ := Hstats (Or.inl hzS)
    exact ⟨hy, statisticalCoreFuture_of_entry_or_reflection ht hdom hstat (Or.inr horbit)⟩
  · subst z
    obtain ⟨p, _, hstat, _, horbit⟩ := Hstats (Or.inr hzS)
    have hy' : mainWallReflection ![θ * ρ, -Real.log ρ, -Real.log ζ] ∈ mainWallChartDomain h := by
      simpa only [mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hy
    have hdom' := hdom
    rw [← normalizedMaxDomain_mainWallReflection h 0 ![θ * ρ, -Real.log ρ, -Real.log ζ]] at hdom'
    exact ⟨hy', statisticalCoreFuture_of_entry_or_reflection ht hdom' hstat (Or.inl horbit)⟩
