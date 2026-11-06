-- Prove2me | solution 1 for BianchiIX.exists_shearRegion_statistics
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:12:19.077018+00:00
-- url     : https://prove2.me/submissions/1ab06b78-300d-481e-a6cb-5f7ab88cfa28

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_RestartFluxData
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalFutureData
import Definitions.Def_BianchiIX_RadialFailureData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_era_joint_statistics
import Theorems.Thm_BianchiIX_exists_restartShearReturn_common_bounds
import Theorems.Thm_BianchiIX_exists_restartShear_common_statistical_preparation
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

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

private theorem BianchiIX.clippedPowerDensityTwo_below {ell B δ x : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hx : 0 < x) (hsmall : B * x ^ δ ≤ ell) :
    clippedPowerDensityTwo ell B δ x = (B / δ) * x ^ (δ - 1) := by
  rw [clippedPowerDensityTwo,
    integral_clippedPowerDensity_of_le (mul_nonneg hB (Real.rpow_nonneg hx.le _)) hδ hsmall,
    Real.rpow_sub hx, Real.rpow_one]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.clippedPowerDensityTwo_above {ell B δ x c : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ)
    (hc0 : 0 < c) (hcx : c ≤ x) (hc : B * c ^ δ = ell) :
    clippedPowerDensityTwo ell B δ x =
      (ell / δ - ell * Real.log c + ell * Real.log x) / x := by
  have hx : 0 < x := hc0.trans_le hcx
  have hp : 0 < B * x ^ δ := mul_pos hB (Real.rpow_pos_of_pos hx _)
  have hlarge : ell ≤ B * x ^ δ := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc0.le hcx hδ.le) hB.le
  have hlog : 0 ≤ Real.log (B * x ^ δ / ell) := Real.log_nonneg ((one_le_div hl).mpr hlarge)
  have hlogell : Real.log ell = Real.log B + δ * Real.log c := by
    rw [← hc, Real.log_mul (ne_of_gt hB) (ne_of_gt (Real.rpow_pos_of_pos hc0 δ)), Real.log_rpow hc0]
  rw [clippedPowerDensityTwo, integral_clippedPowerDensity hl hp hδ,
    min_eq_left hlarge, max_eq_left hlog, Real.log_div (ne_of_gt hp) (ne_of_gt hl),
    Real.log_mul (ne_of_gt hB) (ne_of_gt (Real.rpow_pos_of_pos hx δ)), Real.log_rpow hx, hlogell]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.intervalIntegrable_log_affine_density {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (A D : ℝ) :
    IntervalIntegrable (fun x : ℝ => (A + D * Real.log x) / x) volume c 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc hc1
  apply (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.log ?_))).div continuousOn_id
  · intro x hx
    exact ne_of_gt (hc0.trans_le hx.1)
  · intro x hx
    exact ne_of_gt (hc0.trans_le hx.1)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.integral_log_affine_density {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (A D : ℝ) :
    (∫ x in c..(1 : ℝ), (A + D * Real.log x) / x) =
      -(A * Real.log c + D / 2 * (Real.log c) ^ 2) := by
  have hd (x : ℝ) (hx : x ∈ uIcc c 1) :
      HasDerivAt (fun y => A * Real.log y + D / 2 * (Real.log y) ^ 2)
        ((A + D * Real.log x) / x) x := by
    have hx0 : 0 < x := hc0.trans_le ((uIcc_of_le hc1 ▸ hx).1)
    have H := ((Real.hasDerivAt_log (ne_of_gt hx0)).const_mul A).add
      (((Real.hasDerivAt_log (ne_of_gt hx0)).pow 2).const_mul (D / 2))
    convert! H using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_log_affine_density hc0 hc1 A D)]
  simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.integral_clippedPowerDensityTwo_of_cutoff {ell B δ c : ℝ}
    (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : B * c ^ δ = ell) :
    IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) =
        ell / δ ^ 2 - ell / δ * Real.log c + ell / 2 * (Real.log c) ^ 2 := by
  have hbelow : EqOn (clippedPowerDensityTwo ell B δ) (fun x => (B / δ) * x ^ (δ - 1)) (Ioo 0 c) := by
    intro x hx
    apply clippedPowerDensityTwo_below hB.le hδ hx.1
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1.le hx.2.le hδ.le) hB.le
  have habove : EqOn (clippedPowerDensityTwo ell B δ)
      (fun x => (ell / δ - ell * Real.log c + ell * Real.log x) / x) (Ioo c 1) :=
    fun _ hx => clippedPowerDensityTwo_above hl hB hδ hc0 hx.1.le hc
  have hi0c : IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 c := by
    apply ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < δ - 1)).const_mul (B / δ)).congr_uIoo
    simpa only [uIoo_of_le hc0.le] using hbelow.symm
  have hic1 : IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume c 1 := by
    apply (intervalIntegrable_log_affine_density hc0 hc1 (ell / δ - ell * Real.log c) ell).congr_uIoo
    simpa only [uIoo_of_le hc1] using habove.symm
  refine ⟨hi0c.trans hic1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0c hic1,
    intervalIntegral.integral_congr_Ioo_of_le hc0.le hbelow,
    intervalIntegral.integral_congr_Ioo_of_le hc1 habove,
    integral_power_density hδ,
    integral_log_affine_density hc0 hc1 (ell / δ - ell * Real.log c) ell]
  calc
    _ = (B * c ^ δ) / δ ^ 2 - ell / δ * Real.log c + ell / 2 * (Real.log c) ^ 2 := by ring
    _ = _ := by rw [hc]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.integral_clippedPowerDensityTwo {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) =
        min ell B / δ ^ 2 *
          (1 + max (Real.log (B / ell)) 0 + (max (Real.log (B / ell)) 0) ^ 2 / 2) := by
  by_cases hBl : B ≤ ell
  · have heq : EqOn (clippedPowerDensityTwo ell B δ) (fun x => (B / δ) * x ^ (δ - 1)) (Ioo 0 1) := by
      intro x hx
      apply clippedPowerDensityTwo_below hB.le hδ hx.1
      exact (mul_le_of_le_one_right hB.le (Real.rpow_le_one hx.1.le hx.2.le hδ.le)).trans hBl
    have hi : IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 1 := by
      apply ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < δ - 1)).const_mul (B / δ)).congr_uIoo
      simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using heq.symm
    have hlog : Real.log (B / ell) ≤ 0 := Real.log_nonpos (div_nonneg hB.le hl.le) ((div_le_one hl).mpr hBl)
    refine ⟨hi, ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) heq, integral_power_density hδ,
      min_eq_right hBl, max_eq_right hlog]
    simp
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
    have hlogc : Real.log c = -Real.log (B / ell) / δ := by
      dsimp only [c]
      rw [Real.log_rpow (div_pos hl hB), Real.log_div (ne_of_gt hl) (ne_of_gt hB),
        Real.log_div (ne_of_gt hB) (ne_of_gt hl)]
      ring
    have hlog : 0 ≤ Real.log (B / ell) := Real.log_nonneg ((one_le_div hl).mpr hlB)
    have H := integral_clippedPowerDensityTwo_of_cutoff hl hB hδ hc0 hc1 hc
    refine ⟨H.1, ?_⟩
    rw [H.2, hlogc, min_eq_left hlB, max_eq_left hlog]
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

private theorem BianchiIX.lintegral_clipped_log_two {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (min ell (B * (x * y) ^ δ) / (x * y))) =
      ENNReal.ofReal (min ell B / δ ^ 2 *
        (1 + max (Real.log (B / ell)) 0 + (max (Real.log (B / ell)) 0) ^ 2 / 2)) := by
  have hinner (x : ℝ) (hx : 0 < x) :
      (∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (min ell (B * (x * y) ^ δ) / (x * y))) =
        ENNReal.ofReal (clippedPowerDensityTwo ell B δ x) := by
    have hp : 0 ≤ B * x ^ δ := mul_nonneg hB.le (Real.rpow_nonneg hx.le δ)
    have heq (y : ℝ) (hy : 0 < y) : min ell (B * (x * y) ^ δ) / (x * y) =
        clippedPowerDensity ell (B * x ^ δ) δ y / x := by
      rw [Real.mul_rpow hx.le hy.le, clippedPowerDensity, ← mul_assoc]
      ring
    calc
      _ = ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (clippedPowerDensity ell (B * x ^ δ) δ y / x) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        rw [heq y hy.1]
      _ = ENNReal.ofReal (∫ y in (0 : ℝ)..1, clippedPowerDensity ell (B * x ^ δ) δ y / x) :=
        lintegral_unit_ofReal_eq
          ((intervalIntegrable_clippedPowerDensity hl.le hp hδ (by norm_num)).div_const x)
          (fun _ hy => div_nonneg (clippedPowerDensity_nonneg hl.le hp hy.1.le) hx.le)
      _ = ENNReal.ofReal (clippedPowerDensityTwo ell B δ x) := by
        rw [intervalIntegral.integral_div]
        rfl
  have hnonneg (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ clippedPowerDensityTwo ell B δ x := by
    apply div_nonneg _ hx.1.le
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    exact clippedPowerDensity_nonneg hl.le
      (mul_nonneg hB.le (Real.rpow_nonneg hx.1.le δ)) hy.1
  calc
    _ = ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (clippedPowerDensityTwo ell B δ x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hinner x hx.1
    _ = ENNReal.ofReal (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) :=
      lintegral_unit_ofReal_eq (integral_clippedPowerDensityTwo hl hB hδ).1 hnonneg
    _ = _ := by rw [(integral_clippedPowerDensityTwo hl hB hδ).2]

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

private theorem BianchiIX.hasSum_dyadic_second_moment :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (j + 1)) 6 := by
  have Hc : HasSum (fun j : ℕ => ((j + 2).choose 2 : ℝ) * (1 / 2 : ℝ) ^ j) 8 := by
    convert! hasSum_choose_mul_geometric_of_norm_lt_one 2
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) using 1
    norm_num
  have Hn : HasSum (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) using 1
    norm_num
  convert! ((Hc.mul_left 2).sub (Hn.add hasSum_geometric_two)).mul_left (1 / 2 : ℝ) using 1
  · ext j
    rw [Nat.cast_choose_two]
    push_cast
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
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.hasSum_dyadic_log_square {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    HasSum (fun j => dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)
      (d * ((1 - Real.log d) ^ 2 + 4 * (1 - Real.log d) * Real.log 2 + 6 * (Real.log 2) ^ 2)) := by
  have H := ((hasSum_dyadic_weights.mul_left ((1 - Real.log d) ^ 2)).add
    (hasSum_dyadic_first_moment.mul_left (2 * (1 - Real.log d) * Real.log 2))).add
    (hasSum_dyadic_second_moment.mul_left ((Real.log 2) ^ 2))
  convert! H.mul_left d using 1
  · ext j
    have hlog : Real.log (dyadicScale d j) ≤ 0 :=
      Real.log_nonpos (dyadicScale_pos hd j).le ((dyadicScale_le hd.le j).trans hd1)
    rw [abs_of_nonpos hlog, log_dyadicScale hd]
    dsimp [dyadicScale]
    ring
  · ring

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadic_log_square_sum_le {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    (∑' j, dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2) ≤
      11 * d * (1 + |Real.log d|) ^ 2 := by
  rw [(hasSum_dyadic_log_square hd hd1).tsum_eq,
    abs_of_nonpos (Real.log_nonpos hd.le hd1)]
  have hA : 1 ≤ 1 - Real.log d := by linarith [Real.log_nonpos hd.le hd1]
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hLA : Real.log 2 ≤ 1 - Real.log d := hL1.trans hA
  have hcross := mul_le_mul_of_nonneg_left hLA (by linarith : 0 ≤ 1 - Real.log d)
  have hsquare : (Real.log 2) ^ 2 ≤ (1 - Real.log d) ^ 2 :=
    pow_le_pow_left₀ hL hLA 2
  have H : (1 - Real.log d) ^ 2 + 4 * (1 - Real.log d) * Real.log 2 + 6 * (Real.log 2) ^ 2 ≤
      11 * (1 - Real.log d) ^ 2 := by nlinarith
  calc
    _ ≤ d * (11 * (1 - Real.log d) ^ 2) := mul_le_mul_of_nonneg_left H hd.le
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadic_flux_budget {d C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C) :
    (∑' j, ENNReal.ofReal (C * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2))) ≤
      ENNReal.ofReal (11 * C * d * (1 + |Real.log d|) ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg hC (mul_nonneg (dyadicScale_pos hd j).le (sq_nonneg _)))
    ((hasSum_dyadic_log_square hd hd1).summable.mul_left C), tsum_mul_left]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C * (11 * d * (1 + |Real.log d|) ^ 2) :=
      mul_le_mul_of_nonneg_left (dyadic_log_square_sum_le hd hd1) hC
    _ = _ := by ring

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
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmicFluxConstant_nonneg {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ) :
    0 ≤ logarithmicFluxConstant C δ := by
  have hlog := Real.log_nonneg hC
  unfold logarithmicFluxConstant
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmicLayerCost_le {a C δ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 1 ≤ C) (hδ : 0 < δ) :
    logarithmicLayerCost a C δ ≤
      ENNReal.ofReal (logarithmicFluxConstant C δ * a * (1 + |Real.log a|) ^ 2) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hB : 0 < C * a ^ (-2 * δ) := mul_pos hC0 (Real.rpow_pos_of_pos ha _)
  unfold logarithmicLayerCost
  rw [lintegral_clipped_log_two ha hB hδ]
  apply ENNReal.ofReal_le_ofReal
  let L : ℝ := 1 + |Real.log a|
  let K : ℝ := Real.log C + 1 + 2 * δ
  let z : ℝ := max (Real.log (C * a ^ (-2 * δ) / a)) 0
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hloga : Real.log a ≤ 0 := Real.log_nonpos ha.le ha1
  have hlogs : Real.log (C * a ^ (-2 * δ) / a) = Real.log C + (1 + 2 * δ) * |Real.log a| := by
    rw [Real.log_div (ne_of_gt hB) (ne_of_gt ha),
      Real.log_mul (ne_of_gt hC0) (ne_of_gt (Real.rpow_pos_of_pos ha _)), Real.log_rpow ha,
      abs_of_nonpos hloga]
    ring
  have hz : z = Real.log C + (1 + 2 * δ) * |Real.log a| := by
    dsimp only [z]
    rw [hlogs, max_eq_left (by positivity)]
  have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg (Real.log a)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hz0 : 0 ≤ z := le_max_right _ _
  have hzle : z ≤ K * L := by
    rw [hz]
    dsimp [K, L]
    nlinarith [mul_nonneg hlogC (abs_nonneg (Real.log a))]
  have hsq := pow_le_pow_left₀ hz0 hzle 2
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hKLL := mul_le_mul_of_nonneg_left hLL hK
  have hpoly : 1 + z + z ^ 2 / 2 ≤ (1 + K + K ^ 2 / 2) * L ^ 2 := by
    nlinarith
  have hp : 0 ≤ 1 + z + z ^ 2 / 2 := by positivity
  change min a (C * a ^ (-2 * δ)) / δ ^ 2 * (1 + z + z ^ 2 / 2) ≤
    logarithmicFluxConstant C δ * a * L ^ 2
  calc
    _ ≤ a / δ ^ 2 * (1 + z + z ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg δ)) hp
    _ ≤ a / δ ^ 2 * ((1 + K + K ^ 2 / 2) * L ^ 2) :=
      mul_le_mul_of_nonneg_left hpoly (div_nonneg ha.le (sq_nonneg δ))
    _ = _ := by dsimp [logarithmicFluxConstant, K]; ring

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
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_apply {h : ℝ} {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ mainWallChartDomain h) :
    mainWallMeasure h A = ∫⁻ y in A, ENNReal.ofReal (mainWallChartDensity h y) := by
  rw [mainWallMeasure, withDensity_apply _ hA, Measure.restrict_restrict_of_subset hsub]

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
open Set

private theorem BianchiIX.restartShearFluxDensity_eq_mainWall {h n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    restartShearFluxDensity h n₂ n₃ ρ = mainWallChartDensity h ![ρ, -Real.log n₂, -Real.log n₃] := by
  simp [restartShearFluxDensity, mainWallChartDensity, mainWallChart, mainWallRadicand,
    restartSectionChart, restartSectionRadicand, restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurable_restartShearFluxDensity (h : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => restartShearFluxDensity h p.1.1 p.1.2 p.2) := by
  unfold restartShearFluxDensity correctedSectionFluxDensity sectionFluxDensity shearSq
    restartSectionChart restartSectionRadicand restartShearCurve curvature wallAmplitude
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShear_small_section {h a ε n₂ n₃ ρ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a)
    (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) (hρ : ρ ∈ Icc a (2 * a)) :
    let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
    0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧ x 0 < 0 ∧
      constraint (x 0) ρ h n₂ n₃ = 1 ∧ n₂ ≤ h / 8 ∧ n₃ ≤ h / 8 ∧ |ρ| ≤ 1 / 8 := by
  intro x
  have hε2 : 2 * ε ≤ 1 := by linarith only [hε.2]
  have hn₂ : n₂ ≤ h / 8 := (h₂.2.trans (mul_le_of_le_one_left ha.le hε2)).trans hah
  have hn₃ : n₃ ≤ h / 8 := (h₃.2.trans (mul_le_of_le_one_left ha.le hε2)).trans hah
  have hρ0 : 0 ≤ ρ := ha.le.trans hρ.1
  have hρsmall : |ρ| ≤ 1 / 8 := by
    rw [abs_of_nonneg hρ0]
    linarith only [hρ.2, hah, hh1]
  have hsum : h + n₂ + n₃ ≤ 5 / 4 * h := by linarith only [hn₂, hn₃]
  have H := pow_le_pow_left₀ (add_nonneg (add_nonneg hh.le h₂.1) h₃.1) hsum 2
  have HQ := (abs_le.mp (curvature_abs_le_sum_sq hh.le h₂.1 h₃.1)).2
  have hh2 := pow_le_pow_left₀ hh.le hh1 2
  have hρ2 : ρ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using hρsmall)
  have hrad : 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) := by
    change 0 < 1 - (1 * ρ) ^ 2 - curvature h n₂ n₃
    simp only [one_mul]
    nlinarith only [H, HQ, hh2, hρ2]
  refine ⟨hrad, neg_neg_of_pos (Real.sqrt_pos.mpr hrad), ?_, hn₂, hn₃, hρsmall⟩
  have Hcon := restartSectionChart_constraint hrad.le
  change constraint (x 0) (1 * ρ) h n₂ n₃ = 1 at Hcon
  simpa only [one_mul] using Hcon

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearFluxDensity_bounds {h a ε n₂ n₃ ρ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a)
    (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) (hρ : ρ ∈ Icc a (2 * a)) :
    1 / 2 ≤ restartShearFluxDensity h n₂ n₃ ρ ∧ restartShearFluxDensity h n₂ n₃ ρ ≤ 3 := by
  obtain ⟨_, hp, hcon, hn₂, hn₃, hs⟩ := restartShear_small_section hh hh1 ha hah hε h₂ h₃ hρ
  have H := small_section_corrected_flux_bounds hh hh1 h₂.1 h₃.1 hn₂ hn₃ hs hp hcon
  exact ⟨H.1, H.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallRadicand_eq_shear_abs (h : ℝ) (z : SectionCoordinates) :
    mainWallRadicand h z = restartSectionRadicand h
      (restartShearCurve 1 (Real.exp (-z 1)) (Real.exp (-z 2)) |z 0|) := by
  simp [mainWallRadicand, restartSectionRadicand, restartShearCurve, sq_abs]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChartDensity_eq_shear_abs (h : ℝ) (z : SectionCoordinates) :
    mainWallChartDensity h z =
      restartShearFluxDensity h (Real.exp (-z 1)) (Real.exp (-z 2)) |z 0| := by
  simp [mainWallChartDensity, restartShearFluxDensity, mainWallChart, mainWallRadicand,
    restartSectionChart, restartSectionRadicand, restartShearCurve,
    correctedSectionFluxDensity, sectionFluxDensity, shearSq, sq_abs]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWall_small_shear_abs {h a ε : ℝ} {z : SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (hρ : |z 0| ∈ Icc a (2 * a))
    (h₂ : Real.exp (-z 1) ≤ 2 * ε * a) (h₃ : Real.exp (-z 2) ≤ 2 * ε * a) :
    z ∈ mainWallChartDomain h ∧ 1 / 2 ≤ mainWallChartDensity h z ∧ mainWallChartDensity h z ≤ 3 := by
  refine ⟨?_, ?_⟩
  · change 0 < mainWallRadicand h z
    rw [mainWallRadicand_eq_shear_abs]
    exact (restartShear_small_section hh hh1 ha hah hε
      ⟨(Real.exp_pos _).le, h₂⟩ ⟨(Real.exp_pos _).le, h₃⟩ hρ).1
  · rw [mainWallChartDensity_eq_shear_abs]
    exact restartShearFluxDensity_bounds hh hh1 ha hah hε
      ⟨(Real.exp_pos _).le, h₂⟩ ⟨(Real.exp_pos _).le, h₃⟩ hρ

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.hasFDerivAt_scaledShearLogCoordinates {a : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (h₁ : 0 < z 1) (h₂ : 0 < z 2) :
    HasFDerivAt (scaledShearLogCoordinates a) (scaledShearLogDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).const_mul a).log
      (mul_pos ha h₁).ne').neg
    convert! H using 1
    ext v
    change -(z 1)⁻¹ * v 1 = -((a * z 1)⁻¹ * (a * v 1))
    field_simp
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).const_mul a).log
      (mul_pos ha h₂).ne').neg
    convert! H using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((a * z 2)⁻¹ * (a * v 2))
    field_simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledShearLogDifferential_det (z : SectionCoordinates) :
    (scaledShearLogDifferential z).det = 1 / (z 1 * z 2) := by
  change (scaledShearLogDifferential z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' (scaledShearLogDifferential z).toLinearMap =
      !![1, 0, 0; 0, -(z 1)⁻¹, 0; 0, 0, -(z 2)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, scaledShearLogDifferential]
  rw [H, Matrix.det_fin_three]
  simp [mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledShearLogCoordinates_injOn {a : ℝ} (ha : 0 < a) :
    InjOn (scaledShearLogCoordinates a) {z : SectionCoordinates | 0 < z 1 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change -Real.log (a * z 1) = -Real.log (a * w 1) at h1
  change -Real.log (a * z 2) = -Real.log (a * w 2) at h2
  have H1 := Real.log_injOn_pos (mul_pos ha hz.1) (mul_pos ha hw.1) (neg_injective h1)
  have H2 := Real.log_injOn_pos (mul_pos ha hz.2) (mul_pos ha hw.2) (neg_injective h2)
  ext i
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ ha.ne' H1
  · exact mul_left_cancel₀ ha.ne' H2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledShearLogCoordinates_radicand {a h : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (h₁ : 0 < z 1) (h₂ : 0 < z 2) :
    mainWallRadicand h (scaledShearLogCoordinates a z) =
      restartSectionRadicand h (restartShearCurve 1 (a * z 1) (a * z 2) (z 0)) := by
  simp [mainWallRadicand, scaledShearLogCoordinates, restartSectionRadicand,
    restartShearCurve, Real.exp_log (mul_pos ha h₁), Real.exp_log (mul_pos ha h₂)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_scaledShearLogCoordinates {a h : ℝ} {A : Set SectionCoordinates}
    (ha : 0 < a) (hA : MeasurableSet A)
    (hpos : ∀ z ∈ A, 0 < z 1 ∧ 0 < z 2)
    (hrad : ∀ z ∈ A, 0 < restartSectionRadicand h (restartShearCurve 1 (a * z 1) (a * z 2) (z 0))) :
    mainWallMeasure h (scaledShearLogCoordinates a '' A) =
      ∫⁻ z in A, ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2)) := by
  have hd (z : SectionCoordinates) (hz : z ∈ A) := hasFDerivAt_scaledShearLogCoordinates ha (hpos z hz).1 (hpos z hz).2
  have hi : InjOn (scaledShearLogCoordinates a) A := (scaledShearLogCoordinates_injOn ha).mono hpos
  have himage : MeasurableSet (scaledShearLogCoordinates a '' A) :=
    hA.image_of_continuousOn_injOn (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hi
  have hdom : scaledShearLogCoordinates a '' A ⊆ mainWallChartDomain h := by
    rintro _ ⟨z, hz, rfl⟩
    change 0 < mainWallRadicand h (scaledShearLogCoordinates a z)
    rw [scaledShearLogCoordinates_radicand ha (hpos z hz).1 (hpos z hz).2]
    exact hrad z hz
  rw [mainWallMeasure_apply himage hdom,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA (fun z hz => (hd z hz).hasFDerivWithinAt) hi]
  apply setLIntegral_congr_fun hA
  intro z hz
  change ENNReal.ofReal |(scaledShearLogDifferential z).det| *
    ENNReal.ofReal (mainWallChartDensity h (scaledShearLogCoordinates a z)) = _
  have Hden : mainWallChartDensity h (scaledShearLogCoordinates a z) =
      restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) :=
    (restartShearFluxDensity_eq_mainWall (mul_pos ha (hpos z hz).1) (mul_pos ha (hpos z hz).2)).symm
  rw [scaledShearLogDifferential_det,
    abs_of_pos (one_div_pos.mpr (mul_pos (hpos z hz).1 (hpos z hz).2)),
    Hden,
    ← ENNReal.ofReal_mul (one_div_nonneg.mpr (mul_nonneg (hpos z hz).1.le (hpos z hz).2.le))]
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_shearSectionLayer (a ε : ℝ) : MeasurableSet (shearSectionLayer a ε) := by
  have hρ : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have h₂ : Measurable (fun z : SectionCoordinates => Real.exp (-z 1)) := by fun_prop
  have h₃ : Measurable (fun z : SectionCoordinates => Real.exp (-z 2)) := by fun_prop
  exact (measurableSet_Icc.preimage hρ).inter
    ((measurableSet_le h₂ measurable_const).inter (measurableSet_le h₃ measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_shearUnselectedSection (a ε P : ℝ) : MeasurableSet (shearUnselectedSection a ε P) := by
  have h₂ : Measurable (fun z : SectionCoordinates => Real.exp (-z 1)) := by fun_prop
  have h₃ : Measurable (fun z : SectionCoordinates => Real.exp (-z 2)) := by fun_prop
  exact (measurableSet_shearSectionLayer a ε).inter
    ((measurableSet_lt measurable_const h₂).inter (measurableSet_lt measurable_const h₃))

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

private theorem BianchiIX.shearUnselectedSection_subset_box {a ε P : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hε : ε ≤ 1 / 64) :
    shearUnselectedSection a ε P ⊆
      Icc ![-2 * a, 0, 0] ![2 * a, P * |Real.log a|, P * |Real.log a|] := by
  intro z hz
  have hρ := abs_le.mp hz.1.1.2
  have hε2 : 2 * ε ≤ 1 := by linarith only [hε]
  have hupper : 2 * ε * a ≤ 1 := (mul_le_of_le_one_left ha.le hε2).trans ha1
  have h₂ := logarithmic_wall_window ha ha1 (hz.1.2.1.trans hupper) hz.2.1
  have h₃ := logarithmic_wall_window ha ha1 (hz.1.2.2.trans hupper) hz.2.2
  constructor <;> intro i <;> fin_cases i
  · change -2 * a ≤ z 0
    linarith only [hρ.1]
  · exact h₂.1
  · exact h₃.1
  · exact hρ.2
  · exact h₂.2
  · exact h₃.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_shear_log_box {a P : ℝ} (ha : 0 ≤ a) (hP : 0 ≤ P) :
    volume (Icc ![-2 * a, 0, 0] ![2 * a, P * |Real.log a|, P * |Real.log a|]) =
      ENNReal.ofReal (4 * P ^ 2 * a * |Real.log a| ^ 2) := by
  rw [Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ P * |Real.log a|),
    ← ENNReal.ofReal_mul (by linarith : 0 ≤ 2 * a + 2 * a)]
  congr 1
  ring_nf
  simp only [sq_abs]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_shearUnselectedSection_le {h a ε P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (hP : 0 ≤ P) :
    mainWallMeasure h (shearUnselectedSection a ε P) ≤
      ENNReal.ofReal (12 * P ^ 2 * a * |Real.log a| ^ 2) := by
  have ha1 : a ≤ 1 := by linarith only [hah, hh1]
  have hA := measurableSet_shearUnselectedSection a ε P
  have H (z : SectionCoordinates) (hz : z ∈ shearUnselectedSection a ε P) :=
    mainWall_small_shear_abs hh hh1 ha hah hε hz.1.1 hz.1.2.1 hz.1.2.2
  calc
    _ = ∫⁻ z in shearUnselectedSection a ε P, ENNReal.ofReal (mainWallChartDensity h z) :=
      mainWallMeasure_apply hA (fun z hz => (H z hz).1)
    _ ≤ ∫⁻ _ in shearUnselectedSection a ε P, ENNReal.ofReal (3 : ℝ) :=
      setLIntegral_mono' hA (fun z hz => ENNReal.ofReal_le_ofReal (H z hz).2.2)
    _ = ENNReal.ofReal (3 : ℝ) * volume (shearUnselectedSection a ε P) := by simp
    _ ≤ ENNReal.ofReal (3 : ℝ) * volume
        (Icc ![-2 * a, 0, 0] ![2 * a, P * |Real.log a|, P * |Real.log a|]) :=
      mul_le_mul' le_rfl (measure_mono (shearUnselectedSection_subset_box ha ha1 hε.2))
    _ = _ := by
      rw [volume_shear_log_box ha.le hP, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_shearUnselectedSection_dyadic {h d ε P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (hP : 0 ≤ P) :
    let E := fun j => shearUnselectedSection (dyadicScale d j) ε P
    MeasurableSet (⋃ j : ℕ, E j) ∧
      (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (132 * P ^ 2 * d * (1 + |Real.log d|) ^ 2) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (132 * P ^ 2 * d * (1 + |Real.log d|) ^ 2) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ := by
  intro E
  have hd1 : d ≤ 1 := by linarith only [hdh, hh1]
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤ ENNReal.ofReal
      ((12 * P ^ 2) * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)) := by
    have ha := dyadicScale_pos hd j
    refine (mainWallMeasure_shearUnselectedSection_le hh hh1 ha
      ((dyadicScale_le hd.le j).trans hdh) hε hP).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have H := pow_le_pow_left₀ (abs_nonneg (Real.log (dyadicScale d j)))
      (show |Real.log (dyadicScale d j)| ≤ 1 + |Real.log (dyadicScale d j)| by linarith) 2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H
      (show 0 ≤ 12 * P ^ 2 * dyadicScale d j by positivity)
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤
      ENNReal.ofReal (132 * P ^ 2 * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := ENNReal.tsum_le_tsum Hlayer
    _ ≤ _ := dyadic_flux_budget hd hd1 (show 0 ≤ 12 * P ^ 2 by positivity)
    _ = _ := by congr 1; ring
  have Hunion := (measure_iUnion_le E).trans Hsum
  exact ⟨MeasurableSet.iUnion (fun j => measurableSet_shearUnselectedSection (dyadicScale d j) ε P),
    Hsum, Hunion, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionRadicand_shear_reflection (h σ n₂ n₃ ρ : ℝ) :
    restartSectionRadicand h (restartShearCurve (-σ) n₃ n₂ ρ) =
      restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ) := by
  dsimp [restartSectionRadicand, restartShearCurve, curvature]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionChart_shear_reflection (h σ n₂ n₃ ρ : ℝ) :
    restartSectionChart h (restartShearCurve (-σ) n₃ n₂ ρ) =
      axisSwap (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) := by
  simp only [restartSectionChart, restartSectionRadicand_shear_reflection]
  ext i
  fin_cases i <;> dsimp [restartShearCurve, axisSwap]
  all_goals ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedMaxDomain_shear_reflection (h σ n₂ n₃ ρ t₀ : ℝ) :
    normalizedMaxDomain (restartSectionChart h (restartShearCurve (-σ) n₃ n₂ ρ)) t₀ =
      normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) t₀ := by
  rw [restartSectionChart_shear_reflection]
  exact NormalizedSymmetry.swap.maxDomain _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedMaxCurve_shear_reflection {h σ n₂ n₃ ρ t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) t₀) :
    normalizedMaxCurve (restartSectionChart h (restartShearCurve (-σ) n₃ n₂ ρ)) t₀ t =
      axisSwap (normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) t₀ t) := by
  rw [restartSectionChart_shear_reflection]
  exact NormalizedSymmetry.swap.maxCurve ht

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShear_negative_output_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let x := restartSectionChart h (restartShearCurve (-1) n₂ n₃ ρ)
          let p := restartShearReturnParameters h s n₃ n₂ ρ
          let G := restartShearReturnState h s n₃ n₂ ρ
          let T := restartShearReturnTime h s n₃ n₂ ρ
          0 < restartSectionRadicand h (restartShearCurve (-1) n₂ n₃ ρ) ∧
          0 ≤ s ∧ s < T ∧ T ∈ normalizedMaxDomain x 0 ∧ connectionReturnValid p ∧
          1 / (96 * a) ≤ G 0 ∧ G 0 ≤ 128 / a ∧
          0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
          coreRadiusEntry G = toProjectiveState (normalizedMaxCurve x 0 T) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_common_bounds
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, HA⟩ := HH h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s x p G T
  obtain ⟨hrad, hs, ht, hdom, hp, hlo, hhi, hu, hw, hsum, horbit⟩ :=
    HA a ha ε n₃ n₂ hε h₃ h₂ (by simpa only [min_comm] using hmin) ρ hρ
  refine ⟨?_, hs, ht, ?_, hp, hlo, hhi, hu, hw, ?_, ?_⟩
  · rw [restartSectionRadicand_shear_reflection]
    exact hrad
  · change T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve (-1) n₂ n₃ ρ)) 0
    rw [normalizedMaxDomain_shear_reflection]
    exact hdom
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using hsum
  · change coreRadiusEntry G = toProjectiveState
      (normalizedMaxCurve (restartSectionChart h (restartShearCurve (-1) n₂ n₃ ρ)) 0 T)
    rw [normalizedMaxCurve_shear_reflection hdom, toProjectiveState_axisSwap]
    exact horbit

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChart_restartShear {h τ n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    mainWallChart h ![τ * ρ, -Real.log n₂, -Real.log n₃] =
      restartSectionChart h (restartShearCurve τ n₂ n₃ ρ) := by
  simp [mainWallChart, mainWallRadicand, restartSectionChart, restartSectionRadicand,
    restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallRadicand_restartShear {h τ n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    mainWallRadicand h ![τ * ρ, -Real.log n₂, -Real.log n₃] =
      restartSectionRadicand h (restartShearCurve τ n₂ n₃ ρ) := by
  simp [mainWallRadicand, restartSectionRadicand, restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShear_signed_orbit :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε τ n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (τ = 1 ∨ τ = -1) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let z := if τ = 1 then (n₂, n₃) else (n₃, n₂)
          let y : SectionCoordinates := ![τ * ρ, -Real.log n₂, -Real.log n₃]
          let T := restartShearReturnTime h s z.1 z.2 ρ
          let G := restartShearReturnState h s z.1 z.2 ρ
          y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
            (coreRadiusEntry G = toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T) ∨
              coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T))) := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_common_bounds
  obtain ⟨hN, hhN, HN⟩ := exists_restartShear_negative_output_bounds
  refine ⟨min hA hN, lt_min hhA hhN, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aN, haN, HAN⟩ := HN h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aA aN, lt_min haA haN, ?_⟩
  intro a ha ε τ n₂ n₃ hε hτ h₂ h₃ hmin ρ hρ
  rcases hτ with rfl | rfl
  · simp only [ite_true]
    obtain ⟨hrad, hs, ht, hdom, _, _, _, _, _, _, ho⟩ :=
      HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    refine ⟨?_, hs.trans_lt ht, ?_, Or.inr ?_⟩
    · change 0 < mainWallRadicand h ![1 * ρ, -Real.log n₂, -Real.log n₃]
      rwa [mainWallRadicand_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]
  · simp only [if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    obtain ⟨hrad, hs, ht, hdom, _, _, _, _, _, _, ho⟩ :=
      HAN a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    refine ⟨?_, hs.trans_lt ht, ?_, Or.inl ?_⟩
    · change 0 < mainWallRadicand h ![(-1) * ρ, -Real.log n₂, -Real.log n₃]
      rwa [mainWallRadicand_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartShearCommonLabelSet (ε a P : ℝ) :
    MeasurableSet (restartShearCommonLabelSet ε a P) :=
  ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter
      (measurableSet_le (measurable_fst.min measurable_snd) measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearSection_dyadic_cover {d ε : ℝ} (hd : 0 < d) :
    shearSection d ε = ⋃ j : ℕ, shearSectionAnnulus (dyadicScale d j) ε := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd hz.1
    exact mem_iUnion_of_mem j ⟨hj, hz.2⟩
  · intro hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    have hs : |z 0| ∈ Ioc 0 d := iUnion_dyadicScale_Ioc hd ▸ mem_iUnion_of_mem j hj.1
    exact ⟨hs, hj.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearSectionAnnulus_subset_layer {a ε : ℝ} (hε : 0 ≤ ε) :
    shearSectionAnnulus a ε ⊆ shearSectionLayer a ε := by
  intro z hz
  have H : ε * |z 0| ≤ 2 * ε * a :=
    (mul_le_mul_of_nonneg_left hz.1.2 hε).trans_eq (by ring)
  exact ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2.1.trans H, hz.2.2.trans H⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearSection_selected_representation {a ε P : ℝ} {z : SectionCoordinates}
    (hε : 0 ≤ ε) (hz : z ∈ shearSectionAnnulus a ε) (hn : z ∉ shearUnselectedSection a ε P) :
    ∃ τ n₂ n₃ ρ : ℝ, (τ = 1 ∨ τ = -1) ∧ (n₂, n₃) ∈ restartShearCommonLabelSet ε a P ∧
      ρ ∈ Icc a (2 * a) ∧ z = ![τ * ρ, -Real.log n₂, -Real.log n₃] := by
  have hzL := shearSectionAnnulus_subset_layer hε hz
  have hmin : min (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ a ^ P := by
    by_contra H
    exact hn ⟨hzL, lt_min_iff.mp (lt_of_not_ge H)⟩
  have hl : (Real.exp (-z 1), Real.exp (-z 2)) ∈ restartShearCommonLabelSet ε a P :=
    ⟨⟨Real.exp_pos _, hzL.2.1⟩, ⟨Real.exp_pos _, hzL.2.2⟩, hmin⟩
  by_cases hs : 0 ≤ z 0
  · refine ⟨1, Real.exp (-z 1), Real.exp (-z 2), |z 0|, Or.inl rfl, hl,
      ⟨hz.1.1.le, hz.1.2⟩, ?_⟩
    ext i
    fin_cases i <;> simp [abs_of_nonneg hs]
  · refine ⟨-1, Real.exp (-z 1), Real.exp (-z 2), |z 0|, Or.inr rfl, hl,
      ⟨hz.1.1.le, hz.1.2⟩, ?_⟩
    ext i
    fin_cases i <;> simp [abs_of_neg (lt_of_not_ge hs)]

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

private theorem BianchiIX.exists_restartShear_common_era_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let s := q / 2 * Real.log (1 / a)
              MeasurableSet {p : restartShearCommonLabelSet ε a P × Icc a (2 * a) |
                (p.2 : ℝ) ∈ eraRadialFailure η J σ
                  (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2) Bcap a (2 * a)
                  (restartShearReturnState h s p.1.val.1 p.1.val.2)} ∧
              ∀ n₂ n₃ : ℝ, (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
                min n₂ n₃ ≤ a ^ P →
                let B := restartShearAmplitudeBudget a n₂ n₃
                let Y := restartShearReturnState h s n₂ n₃
                let F := eraRadialFailure η J σ B Bcap a (2 * a) Y
                B ∈ Ioc 0 Bcap ∧ MeasurableSet F ∧
                  (∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc a (2 * a) →
                    ∀ (ω : ℝ → ℝ≥0∞) (M : ℝ), 0 ≤ M → (∀ ρ ∈ A, ω ρ ≤ ENNReal.ofReal M) →
                      (∫⁻ ρ in A ∩ F, ω ρ) ≤ min (∫⁻ ρ in A, ω ρ)
                        (ENNReal.ofReal (320 * Real.sqrt 3 * M * B ^ σ))) ∧
                  ∀ ρ ∈ Icc a (2 * a), ρ ∉ F →
                    ∃ p : eraSurvivorDomain η J σ Bcap, p.val = (B, Y ρ) ∧
                      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_joint_statistics hBirkhoff
  obtain ⟨hstar, hhstar, HP⟩ := exists_restartShear_common_statistical_preparation
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, htyp, Bs, hBs, hBscap, Hstats⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, Ha⟩ := HP h hh q D P hq hD hP Bs hBs
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε hε s
  obtain ⟨hY, Hcurve⟩ := Ha a ha ε hε
  refine ⟨?_, ?_⟩
  · have hbad := htyp.compl.preimage hY
    convert! hbad using 1
    ext p
    change ((p.2 : ℝ) ∈ Icc a (2 * a) ∧
      (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2,
        restartShearReturnState h s p.1.val.1 p.1.val.2 p.2) ∉
        EraSurvivor.typicalDomain η J σ Bcap) ↔ _
    exact and_iff_right p.2.property
  · intro n₂ n₃ h₂ h₃ hmin B Y F
    obtain ⟨hB, hΓ, Hradial⟩ := Hcurve n₂ n₃ h₂ h₃ hmin
    let Γ := restartShearEraCurve h s n₂ n₃ a
    let f := restartShearReturnPhase h s n₂ n₃
    obtain ⟨hG, _, Hloss, Hgood⟩ := Hstats B hB Γ hΓ
    have hloss : volume (Ioo 0 1 \ EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ≤ ENNReal.ofReal (80 * B ^ σ) := by
      simpa only [univ_inter] using (Hloss univ).trans (min_le_right _ _)
    have Hfail := era_radial_failure_weighted (Γ := Γ) (Y := Y) (f := f)
      (by positivity : 0 < 1 / (4 * Real.sqrt (3 : ℝ)))
      (fun ρ hρ => (Hradial ρ hρ).2.1) (fun ρ hρ => (Hradial ρ hρ).2.2.1)
      (fun ρ hρ => (Hradial ρ hρ).1) (fun ρ hρ => (Hradial ρ hρ).2.2.2) hG hloss
    refine ⟨⟨hB.1, hB.2.trans hBscap⟩, Hfail.1, ?_, ?_⟩
    · intro A hA hAI ω M hM hω
      have H := Hfail.2 A hA hAI ω M hM hω
      have hcoef : ENNReal.ofReal (M / (1 / (4 * Real.sqrt 3))) * ENNReal.ofReal (80 * B ^ σ) =
          ENNReal.ofReal (320 * Real.sqrt 3 * M * B ^ σ) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ M / (1 / (4 * Real.sqrt 3)))]
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
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.restartShearRadialFlux_le {h a ε n₂ n₃ : ℝ} {A : Set ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a)
    (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) (hA : A ⊆ Icc a (2 * a)) :
    restartShearRadialFlux h n₂ n₃ A ≤ ENNReal.ofReal (3 * a) := by
  calc
    _ ≤ ∫⁻ ρ in Icc a (2 * a), ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ) :=
      lintegral_mono_set hA
    _ ≤ ∫⁻ _ in Icc a (2 * a), ENNReal.ofReal (3 : ℝ) :=
      setLIntegral_mono' measurableSet_Icc (fun ρ hρ =>
        ENNReal.ofReal_le_ofReal (restartShearFluxDensity_bounds hh hh1 ha hah hε h₂ h₃ hρ).2)
    _ = _ := by simp [Real.volume_Icc, show 2 * a - a = a by ring, ENNReal.ofReal_mul]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.mem_shearLabelFailureSection_image_iff {a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} {z : SectionCoordinates} (ha : 0 < a) (hz : 0 < z 1 ∧ 0 < z 2) :
    scaledShearLogCoordinates a z ∈ shearLabelFailureSection a L F ↔
      z ∈ shearLabelFailureCoordinates a L F := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact scaledShearLogCoordinates_injOn ha ⟨hw.1.1, hw.2.1.1⟩ hz heq ▸ hw
  · exact fun hw => ⟨z, hw, rfl⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.mem_shearLabelFailureSection_iff {a n₂ n₃ ρ : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (ha : 0 < a) (h₂ : n₂ ∈ Ioo 0 a) (h₃ : n₃ ∈ Ioo 0 a)
    (hl : (n₂, n₃) ∈ L) :
    ![ρ, -Real.log n₂, -Real.log n₃] ∈ shearLabelFailureSection a L F ↔ ρ ∈ F (n₂, n₃) := by
  have hx : n₂ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos h₂.1 ha, (div_lt_one ha).mpr h₂.2⟩
  have hy : n₃ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos h₃.1 ha, (div_lt_one ha).mpr h₃.2⟩
  have h₂a : a * (n₂ / a) = n₂ := mul_div_cancel₀ _ ha.ne'
  have h₃a : a * (n₃ / a) = n₃ := mul_div_cancel₀ _ ha.ne'
  have H := mem_shearLabelFailureSection_image_iff (L := L) (F := F)
    (z := ![ρ, n₂ / a, n₃ / a]) ha ⟨hx.1, hy.1⟩
  simpa [scaledShearLogCoordinates, shearLabelFailureCoordinates, h₂a, h₃a,
    hx.1, hx.2, hy.1, hy.2, hl] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.measurableSet_shearLabelFailureCoordinates {a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (hL : MeasurableSet L)
    (hFI : ∀ z ∈ L, F z ⊆ Icc a (2 * a))
    (hjoint : MeasurableSet {p : L × Icc a (2 * a) | (p.2 : ℝ) ∈ F p.1.val}) :
    MeasurableSet (shearLabelFailureCoordinates a L F) := by
  let D : Set SectionCoordinates := {z | (a * z 1, a * z 2) ∈ L ∧ z 0 ∈ Icc a (2 * a)}
  have hD : MeasurableSet D := (hL.preimage (by fun_prop)).inter
    (measurableSet_Icc.preimage (measurable_pi_apply 0))
  let g : D → L × Icc a (2 * a) := fun z =>
    (⟨(a * z.val 1, a * z.val 2), z.property.1⟩, ⟨z.val 0, z.property.2⟩)
  have hg : Measurable g := by
    apply Measurable.prodMk
    · apply Measurable.subtype_mk
      exact (measurable_const.mul ((measurable_pi_apply 1).comp measurable_subtype_coe)).prodMk
        (measurable_const.mul ((measurable_pi_apply 2).comp measurable_subtype_coe))
    · exact ((measurable_pi_apply 0).comp measurable_subtype_coe).subtype_mk
  have H := hD.subtype_image (hjoint.preimage hg)
  have heq : Subtype.val '' g ⁻¹' {p : L × Icc a (2 * a) | (p.2 : ℝ) ∈ F p.1.val} =
      {z : SectionCoordinates | (a * z 1, a * z 2) ∈ L ∧ z 0 ∈ F (a * z 1, a * z 2)} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property.1, hw⟩
    · intro hz
      exact ⟨⟨z, hz.1, hFI _ hz.1 hz.2⟩, hz.2, rfl⟩
  rw [heq] at H
  exact (measurableSet_Ioo.preimage (measurable_pi_apply 1)).inter
    ((measurableSet_Ioo.preimage (measurable_pi_apply 2)).inter H)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.measurableSet_shearLabelFailureSection {a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (ha : 0 < a) (hA : MeasurableSet (shearLabelFailureCoordinates a L F)) :
    MeasurableSet (shearLabelFailureSection a L F) := by
  apply hA.image_of_continuousOn_injOn
  · intro z hz
    exact (hasFDerivAt_scaledShearLogCoordinates ha hz.1.1 hz.2.1.1).continuousAt.continuousWithinAt
  · apply (scaledShearLogCoordinates_injOn ha).mono
    intro z hz
    exact ⟨hz.1.1, hz.2.1.1⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.shearLabelFailureCoordinates_lintegral {h a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (hA : MeasurableSet (shearLabelFailureCoordinates a L F)) :
    (∫⁻ z in shearLabelFailureCoordinates a L F,
      ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2))) =
      shearLabelFailureLayer h a L F := by
  let A := shearLabelFailureCoordinates a L F
  let f : SectionCoordinates → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2))
  have hf : Measurable f := by
    have hg : Measurable (fun z : SectionCoordinates => ((a * z 1, a * z 2), z 0)) := by fun_prop
    have hd : Measurable (fun z : SectionCoordinates =>
        restartShearFluxDensity h (a * z 1) (a * z 2) (z 0)) := by
      simpa only [Function.comp_def] using (measurable_restartShearFluxDensity h).comp hg
    exact (hd.div ((measurable_pi_apply 1).mul (measurable_pi_apply 2))).ennreal_ofReal
  change (∫⁻ z in A, f z) = _
  rw [← lintegral_indicator hA, lintegral_three_coordinates (hf.indicator hA)]
  unfold shearLabelFailureLayer
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases hx : 0 < x ∧ x < 1
  · rw [indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from hx), ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro y
    by_cases hy : 0 < y ∧ y < 1
    · rw [indicator_of_mem (show y ∈ Ioo (0 : ℝ) 1 from hy)]
      by_cases hl : (a * x, a * y) ∈ L
      · rw [if_pos hl]
        have hF : MeasurableSet (F (a * x, a * y)) := by
          have H := hA.preimage (show Measurable (fun r : ℝ => ![r, x, y]) by fun_prop)
          simpa [shearLabelFailureCoordinates, hx, hy, hl] using H
        have heq : (fun r => A.indicator f ![r, x, y]) =
            (F (a * x, a * y)).indicator
              (fun r => ENNReal.ofReal (restartShearFluxDensity h (a * x) (a * y) r / (x * y))) := by
          funext r
          simp [indicator, A, shearLabelFailureCoordinates, f, hx, hy, hl]
        rw [heq, lintegral_indicator hF]
        simp_rw [ENNReal.ofReal_div_of_pos (mul_pos hx.1 hy.1), div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr
          (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hx.1 hy.1))))
      · simp [indicator, shearLabelFailureCoordinates, hl]
    · simp [indicator, shearLabelFailureCoordinates, hy]
  · simp [indicator, shearLabelFailureCoordinates, hx]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.mainWallMeasure_shearLabelFailureSection {h a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (ha : 0 < a) (hA : MeasurableSet (shearLabelFailureCoordinates a L F))
    (hrad : ∀ z ∈ shearLabelFailureCoordinates a L F,
      0 < restartSectionRadicand h (restartShearCurve 1 (a * z 1) (a * z 2) (z 0))) :
    mainWallMeasure h (shearLabelFailureSection a L F) = shearLabelFailureLayer h a L F := by
  rw [shearLabelFailureSection, mainWallMeasure_scaledShearLogCoordinates ha hA
    (fun z hz => ⟨hz.1.1, hz.2.1.1⟩) hrad]
  exact shearLabelFailureCoordinates_lintegral hA

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.shearLabelFailureLayer_le {h a C σ : ℝ} {L : Set (ℝ × ℝ)} {F : ℝ × ℝ → Set ℝ}
    (Hslice : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, (a * x, a * y) ∈ L →
      restartShearRadialFlux h (a * x) (a * y) (F (a * x, a * y)) ≤
        ENNReal.ofReal (3 * min a ((C * a ^ (-2 * σ)) * (x * y) ^ σ))) :
    shearLabelFailureLayer h a L F ≤ 3 * logarithmicLayerCost a C σ := by
  let f := fun x y : ℝ => ENNReal.ofReal (min a ((C * a ^ (-2 * σ)) * (x * y) ^ σ) / (x * y))
  have Hpoint (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
      (if (a * x, a * y) ∈ L then
        restartShearRadialFlux h (a * x) (a * y) (F (a * x, a * y)) / ENNReal.ofReal (x * y)
        else 0) ≤ 3 * f x y := by
    split_ifs with hl
    · have H := ENNReal.div_le_div_right (Hslice x hx y hy hl) (ENNReal.ofReal (x * y))
      refine H.trans_eq ?_
      rw [← ENNReal.ofReal_div_of_pos (mul_pos hx.1 hy.1)]
      change ENNReal.ofReal (3 * min a _ / (x * y)) = 3 * ENNReal.ofReal (min a _ / (x * y))
      rw [show (3 : ℝ) * min a _ / (x * y) = 3 * (min a _ / (x * y)) by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    · exact zero_le
  calc
    _ ≤ ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1, 3 * f x y :=
      setLIntegral_mono' measurableSet_Ioo (fun x hx =>
        setLIntegral_mono' measurableSet_Ioo (fun y hy => Hpoint x y hx hy))
    _ = _ := by
      simp_rw [lintegral_const_mul' (3 : ℝ≥0∞) _ (by norm_num)]
      rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.shearFailureFluxConstant_ge_one {σ : ℝ} (hσ : 0 ≤ σ) : 1 ≤ shearFailureFluxConstant σ := by
  have hp : 1 ≤ (800 : ℝ) ^ σ := Real.one_le_rpow (by norm_num) hσ
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have H := mul_le_mul hs hp (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)
  dsimp only [shearFailureFluxConstant]
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.restartShearAmplitudeBudget_normalized {a x y σ : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    640 * Real.sqrt 3 * (restartShearAmplitudeBudget a (a * x) (a * y)) ^ σ =
      (shearFailureFluxConstant σ * a ^ (-2 * σ)) * (x * y) ^ σ := by
  have hB : restartShearAmplitudeBudget a (a * x) (a * y) =
      800 * (a ^ (-2 : ℝ) * (x * y)) := by
    rw [Real.rpow_neg ha.le, Real.rpow_two]
    unfold restartShearAmplitudeBudget
    field_simp
  rw [hB, Real.mul_rpow (by norm_num) (mul_nonneg (Real.rpow_nonneg ha.le _) (mul_nonneg hx hy)),
    Real.mul_rpow (Real.rpow_nonneg ha.le _) (mul_nonneg hx hy), ← Real.rpow_mul ha.le]
  dsimp only [shearFailureFluxConstant]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mem_restartShearCommonFailureSection_iff {h s a ε P η σ Bcap n₂ n₃ ρ : ℝ} {J : ℕ}
    (ha : 0 < a) (hε : ε ≤ 1 / 128) (hl : (n₂, n₃) ∈ restartShearCommonLabelSet ε a P) :
    ![ρ, -Real.log n₂, -Real.log n₃] ∈ restartShearCommonFailureSection h s a ε P η J σ Bcap ↔
      ρ ∈ restartShearFailureFibers h s a η J σ Bcap (n₂, n₃) := by
  have hs : 2 * ε < 1 := by linarith only [hε]
  exact mem_shearLabelFailureSection_iff ha
    ⟨hl.1.1, hl.1.2.trans_lt (mul_lt_of_lt_one_left ha hs)⟩
    ⟨hl.2.1.1, hl.2.1.2.trans_lt (mul_lt_of_lt_one_left ha hs)⟩ hl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restartShear_common_physical_failure (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let s := q / 2 * Real.log (1 / a)
              let E := restartShearCommonFailureSection h s a ε P η J σ Bcap
              let K := 3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              MeasurableSet E ∧ mainWallMeasure h E = restartShearCommonFailureLayer h s a ε P η J σ Bcap ∧
                mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) ∧
                mainWallMeasure h E ≠ ⊤ ∧
                ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearCommonLabelSet ε a P →
                  ∀ ρ ∈ Icc a (2 * a), ![ρ, -Real.log n₂, -Real.log n₃] ∉ E →
                    ∃ p : eraSurvivorDomain η J σ Bcap,
                      p.val = (restartShearAmplitudeBudget a n₂ n₃, restartShearReturnState h s n₂ n₃ ρ) ∧
                      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_common_era_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh q D P hq hD hP
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  refine ⟨min aS (min (h / 8) 1), lt_min haS (lt_min (div_pos hh.1 (by norm_num)) zero_lt_one), ?_⟩
  intro a ha ε hε s E K
  have hah : a ≤ h / 8 := ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε64 : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, hε.2.trans (by norm_num)⟩
  obtain ⟨hjoint, Hstats⟩ := HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε hε
  let L := restartShearCommonLabelSet ε a P
  let F := restartShearFailureFibers h s a η J σ Bcap
  have hFI : ∀ z ∈ L, F z ⊆ Icc a (2 * a) := fun _ _ _ hρ => hρ.1
  have hA := measurableSet_shearLabelFailureCoordinates
    (measurableSet_restartShearCommonLabelSet ε a P) hFI hjoint
  have heq : mainWallMeasure h E = restartShearCommonFailureLayer h s a ε P η J σ Bcap := by
    apply mainWallMeasure_shearLabelFailureSection ha.1 hA
    intro z hz
    have hl := hz.2.2.1
    exact (restartShear_small_section hh.1 hh1 ha.1 hah hε64
      ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ (hFI _ hl hz.2.2.2)).1
  have Hslice (n₂ n₃ : ℝ) (hl : (n₂, n₃) ∈ L) :
      restartShearRadialFlux h n₂ n₃ (F (n₂, n₃)) ≤
        ENNReal.ofReal (3 * min a (640 * Real.sqrt 3 * (restartShearAmplitudeBudget a n₂ n₃) ^ σ)) := by
    obtain ⟨hB, hF, Hloss, _⟩ := Hstats n₂ n₃ hl.1 hl.2.1 hl.2.2
    have H := (Hloss (F (n₂, n₃)) hF (hFI _ hl)
      (fun ρ => ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ)) 3 (by norm_num)
      (fun ρ hρ => ENNReal.ofReal_le_ofReal
        (restartShearFluxDensity_bounds hh.1 hh1 ha.1 hah hε64
          ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ (hFI _ hl hρ)).2)).trans (min_le_right _ _)
    change (∫⁻ ρ in F (n₂, n₃) ∩ F (n₂, n₃), _) ≤ _ at H
    rw [inter_self] at H
    by_cases hm : a ≤ 640 * Real.sqrt 3 * (restartShearAmplitudeBudget a n₂ n₃) ^ σ
    · rw [min_eq_left hm]
      exact restartShearRadialFlux_le hh.1 hh1 ha.1 hah hε64
        ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ (hFI _ hl)
    · rw [min_eq_right (le_of_not_ge hm)]
      refine H.trans (ENNReal.ofReal_le_ofReal ?_)
      nlinarith only [mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.rpow_nonneg hB.1.le σ)]
  have Hlayer : restartShearCommonFailureLayer h s a ε P η J σ Bcap ≤
      3 * logarithmicLayerCost a (shearFailureFluxConstant σ) σ := by
    apply shearLabelFailureLayer_le
    intro x hx y hy hl
    simpa only [restartShearAmplitudeBudget_normalized ha.1 hx.1.le hy.1.le] using Hslice (a * x) (a * y) hl
  have Hbound : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) := calc
    _ = _ := heq
    _ ≤ _ := Hlayer
    _ ≤ 3 * ENNReal.ofReal (logarithmicFluxConstant (shearFailureFluxConstant σ) σ * a * (1 + |Real.log a|) ^ 2) :=
      mul_le_mul' le_rfl (logarithmicLayerCost_le ha.1 ha1 (shearFailureFluxConstant_ge_one hσ.le) hσ)
    _ = _ := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_shearLabelFailureSection ha.1 hA, heq, Hbound,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro n₂ n₃ hl ρ hρ hn
  exact (Hstats n₂ n₃ hl.1 hl.2.1 hl.2.2).2.2.2 ρ hρ
    (fun hbad => hn ((mem_restartShearCommonFailureSection_iff ha.1 hε.2 hl).mpr hbad))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mem_restartShearCommonLabelSet_swap {ε a P n₂ n₃ : ℝ}
    (hl : (n₂, n₃) ∈ restartShearCommonLabelSet ε a P) :
    (n₃, n₂) ∈ restartShearCommonLabelSet ε a P :=
  ⟨hl.2.1, hl.1, by simpa only [min_comm] using hl.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.restartShearAmplitudeBudget_swap (a n₂ n₃ : ℝ) :
    restartShearAmplitudeBudget a n₃ n₂ = restartShearAmplitudeBudget a n₂ n₃ := by
  unfold restartShearAmplitudeBudget
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restartShear_signed_physical_failure (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let s := q / 2 * Real.log (1 / a)
              let E := mainWallSymmetrization (restartShearCommonFailureSection h s a ε P η J σ Bcap)
              let K := 6 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              MeasurableSet E ∧ mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) ∧
                mainWallMeasure h E ≠ ⊤ ∧
                ∀ τ : ℝ, (τ = 1 ∨ τ = -1) →
                  ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearCommonLabelSet ε a P →
                    ∀ ρ ∈ Icc a (2 * a), ![τ * ρ, -Real.log n₂, -Real.log n₃] ∉ E →
                      let z := if τ = 1 then (n₂, n₃) else (n₃, n₂)
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartShearAmplitudeBudget a n₂ n₃, restartShearReturnState h s z.1 z.2 ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_common_physical_failure hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε hε s E K
  obtain ⟨hE, _, Hbound, _, Hgood⟩ := Ha a ha ε hε
  have Hsigned : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) := calc
    _ ≤ _ := mainWallMeasure_symmetrization_le hE
    _ ≤ 2 * ENNReal.ofReal
        (3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ * a * (1 + |Real.log a|) ^ 2) :=
      mul_le_mul' le_rfl Hbound
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_mainWallSymmetrization hE, Hsigned,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hsigned, ?_⟩
  intro τ hτ n₂ n₃ hl ρ hρ hn
  rcases hτ with rfl | rfl
  · have hn' : ![ρ, -Real.log n₂, -Real.log n₃] ∉
        restartShearCommonFailureSection h s a ε P η J σ Bcap := by
      intro hbad
      apply hn
      rw [one_mul]
      exact Or.inl hbad
    simpa only [if_pos rfl, ite_true] using Hgood n₂ n₃ hl ρ hρ hn'
  · have hn' : ![ρ, -Real.log n₃, -Real.log n₂] ∉
        restartShearCommonFailureSection h s a ε P η J σ Bcap := by
      intro hbad
      apply hn
      have H : mainWallReflection ![ρ, -Real.log n₃, -Real.log n₂] ∈ E := Or.inr ⟨_, hbad, rfl⟩
      change ![-ρ, -Real.log n₂, -Real.log n₃] ∈ E at H
      simpa only [neg_one_mul] using H
    obtain ⟨p, hp, hstat⟩ := Hgood n₃ n₂ (mem_restartShearCommonLabelSet_swap hl) ρ hρ hn'
    refine ⟨p, ?_, hstat⟩
    simpa only [if_neg (by norm_num : (-1 : ℝ) ≠ 1), restartShearAmplitudeBudget_swap a n₂ n₃] using hp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_restartShear_signed_physical_failure_dyadic (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let E := fun j => mainWallSymmetrization (restartShearCommonFailureSection h
                (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ Bcap)
              let C := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              (∀ j : ℕ, MeasurableSet (E j)) ∧ MeasurableSet (⋃ j : ℕ, E j) ∧
                (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ ∧
                ∀ j : ℕ, ∀ τ : ℝ, (τ = 1 ∨ τ = -1) →
                  ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearCommonLabelSet ε (dyadicScale d j) P →
                    ∀ ρ ∈ Icc (dyadicScale d j) (2 * dyadicScale d j),
                      ![τ * ρ, -Real.log n₂, -Real.log n₃] ∉ ⋃ i : ℕ, E i →
                      let z := if τ = 1 then (n₂, n₃) else (n₃, n₂)
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartShearAmplitudeBudget (dyadicScale d j) n₂ n₃,
                          restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) z.1 z.2 ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_signed_physical_failure hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q D P hq hD hP
  refine ⟨min astar 1, lt_min hastar zero_lt_one, ?_⟩
  intro d hd ε hε E C
  have Hdata (j : ℕ) := Ha (dyadicScale d j)
    ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩ ε hε
  have hE (j : ℕ) : MeasurableSet (E j) := (Hdata j).1
  let K := 6 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
  have hK : 0 ≤ K := mul_nonneg (by norm_num)
    (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ)
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤ ENNReal.ofReal
      (K * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)) := by
    simpa only [E, K, mul_assoc] using (Hdata j).2.1
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := ENNReal.tsum_le_tsum Hlayer
    _ ≤ _ := dyadic_flux_budget hd.1 (hd.2.trans (min_le_right _ _)) hK
    _ = _ := by congr 1; dsimp only [C, K]; ring
  have Hunion := (measure_iUnion_le E).trans Hsum
  refine ⟨hE, MeasurableSet.iUnion hE, Hsum, Hunion,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion, ?_⟩
  intro j τ hτ n₂ n₃ hl ρ hρ hn
  exact (Hdata j).2.2.2 τ hτ n₂ n₃ hl ρ hρ (fun hbad => hn (mem_iUnion_of_mem j hbad))

end
end

/-- Every point of the full shear-dominated region outside one finite-flux Borel set reaches a statistical core along its exact Einstein orbit. -/
theorem solution (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let F := shearFailureRegion h q d ε P η J σ Bcap
              let C := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ + 132 * P ^ 2
              MeasurableSet F ∧ mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h F ≠ ⊤ ∧
                ∀ z ∈ shearSection d ε \ F,
                  z ∈ mainWallChartDomain h ∧ StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_signed_physical_failure_dyadic hBirkhoff
  obtain ⟨hO, hhO, HO⟩ := exists_restartShear_signed_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (min hO (1 / 8)), lt_min hhS (lt_min hhO (by norm_num)), ?_⟩
  intro h hh q D P hq hD hP
  have hh' := hh.2.trans (min_le_right _ _)
  have hh1 : h ≤ 1 / 8 := hh'.trans (min_le_right _ _)
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aO, haO, HaO⟩ := HO h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hP
  refine ⟨min dS (min aO (h / 8)), lt_min hdS (lt_min haO (div_pos hh.1 (by norm_num))), ?_⟩
  intro d hd ε hε F C
  have hdh : d ≤ h / 8 := hd.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdO : d ≤ aO := hd.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε64 : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, hε.2.trans (by norm_num)⟩
  let S := ⋃ j : ℕ, mainWallSymmetrization (restartShearCommonFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ Bcap)
  let U := ⋃ j : ℕ, shearUnselectedSection (dyadicScale d j) ε P
  let K := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
  let A := 132 * P ^ 2
  obtain ⟨_, hS, _, HSbound, _, Hgood⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩ ε hε
  obtain ⟨hU, _, HUbound, _⟩ := mainWallMeasure_shearUnselectedSection_dyadic hh.1 hh1 hd.1 hdh hε64
    (by linarith only [hD, hP] : 0 ≤ P)
  have hK : 0 ≤ K := mul_nonneg (by norm_num)
    (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hW : 0 ≤ (1 + |Real.log d|) ^ 2 := sq_nonneg _
  have Hbound : mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ mainWallMeasure h S + mainWallMeasure h U := measure_union_le S U
    _ ≤ ENNReal.ofReal (K * d * (1 + |Real.log d|) ^ 2) +
        ENNReal.ofReal (A * d * (1 + |Real.log d|) ^ 2) := add_le_add HSbound HUbound
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hK hd.1.le) hW)
        (mul_nonneg (mul_nonneg hA hd.1.le) hW)]
      congr 1
      change K * d * _ + A * d * _ = (K + A) * d * _
      ring
  refine ⟨hS.union hU, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro z hz
  have hcover : z ∈ ⋃ j : ℕ, shearSectionAnnulus (dyadicScale d j) ε := by
    rw [← shearSection_dyadic_cover hd.1]
    exact hz.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
  have hzS : z ∉ S := fun hbad => hz.2 (Or.inl hbad)
  have hzU : z ∉ shearUnselectedSection (dyadicScale d j) ε P :=
    fun hbad => hz.2 (Or.inr (mem_iUnion_of_mem j hbad))
  obtain ⟨τ, n₂, n₃, ρ, hτ, hl, hρ, rfl⟩ := shearSection_selected_representation hε.1 hj hzU
  obtain ⟨p, hp, hstat⟩ := Hgood j τ hτ n₂ n₃ hl ρ hρ hzS
  obtain ⟨hy, ht, hdom, ho⟩ := HaO (dyadicScale d j)
    ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans hdO⟩
    ε τ n₂ n₃ hε hτ hl.1 hl.2.1 hl.2.2 ρ hρ
  exact ⟨hy, statisticalCoreFuture_of_entry_or_reflection ht hdom hstat (by simpa only [hp] using ho)⟩
