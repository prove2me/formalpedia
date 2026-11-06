-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_projection_error
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:53:31.572243+00:00
-- url     : https://prove2.me/submissions/59e5ee9b-81bd-43bc-adc2-a912a7ef31b4

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_RadialTransportData
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_compact_vanishing_slice_bounds
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_exists_restartShearTail_radial_control
import Theorems.Thm_BianchiIX_exists_rpow_log_quadratic_scale
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_shearTail_constraint_bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_wall_rates {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    rateOne p s ≤ -2 ∧ |rateTwo p s| ≤ 6 * a ∧ rateThree p s ≤ -a / 2 := by
  obtain ⟨hQ, _, _, _, hp', hAl, hAu⟩ := shearTail_constraint_bounds ha hp hs hn hx hy hc
  have HC : p ^ 2 + s ^ 2 + curvature n x y = 1 := hc
  have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
  have hs0 : 0 ≤ s := by linarith only [hs.1, ha.1]
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hrl : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by nlinarith only [hr0, hr2]
  have hru : Real.sqrt 3 ≤ (7 : ℝ) / 4 := by nlinarith only [hr0, hr2]
  have hRslo := mul_le_mul hrl hs.1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 2) hr0
  have hRshi := mul_le_mul hru hs.2 hs0 (by norm_num : (0 : ℝ) ≤ 7 / 4)
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp only [rateOne, shearSq]
    nlinarith only [hp', sq_nonneg (p + 15 / 16), sq_nonneg s]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).1, hAu, hRslo, ha2, ha.1]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRshi, ha2, ha.1, sq_nonneg a]
  · dsimp only [rateThree, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRslo, ha2, ha.1, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_shear_rate {a s n x y : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1 / 256) (hs : |s| ≤ 3 * a)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |shearMinus s n x y| ≤ 3 * (x ^ 2 + y ^ 2 + n * (x + y) + a * n ^ 2) := by
  have hQ : |curvature n x y| ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y) := by
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg n, sq_nonneg (x - y)]
    · nlinarith only [mul_nonneg hx hy, mul_nonneg hn (add_nonneg hx hy)]
  have hH : |-x ^ 2 + y ^ 2 + n * x - n * y| ≤ x ^ 2 + y ^ 2 + n * (x + y) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hn hx, mul_nonneg hn hy]
  have hr : |Real.sqrt 3| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have HQ := mul_le_mul hQ hs (abs_nonneg _) (by positivity : 0 ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y))
  have HH := mul_le_mul hr hH (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H := abs_add_le (curvature n x y * s) (Real.sqrt 3 * (-x ^ 2 + y ^ 2 + n * x - n * y))
  rw [abs_mul, abs_mul] at H
  have Hsmall := mul_nonneg (show 0 ≤ 1 - 6 * a by linarith only [ha.2])
    (show 0 ≤ x ^ 2 + y ^ 2 + n * (x + y) by positivity)
  dsimp only [shearMinus]
  nlinarith only [H, HQ, HH, Hsmall, mul_nonneg ha.1 (add_nonneg (sq_nonneg x) (sq_nonneg y))]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.abs_sub_le_of_deriv_primitive {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t) :
    ∀ t ∈ Icc a b, |f t - f a| ≤ z t - z a := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [le_abs_self (f' s), hb s hs]) ha ht ht.1
  have HL := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg.sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [zero_mul, Real.exp_zero, mul_one, Pi.sub_apply, Pi.neg_apply] at HU HL
  exact abs_le.mpr ⟨by linarith only [HL], by linarith only [HU]⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_shearTailDrift {a : ℝ} (ha : a ≠ 0) (A X Y t : ℝ) :
    HasDerivAt (shearTailDrift a A X Y)
      (3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
        a * A / 4 * Real.exp (-2 * t)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-a)).exp.const_sub 1).const_mul (3 * Y ^ 2 / a)).add
    ((((hasDerivAt_id' t).const_mul (12 * a)).exp.sub_const 1).const_mul (X ^ 2 / (4 * a)))).add
      ((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (a * A / 8)) using 1
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTailDrift_le {a A X Y T t : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (ht : t ≤ T) :
    shearTailDrift a A X Y t ≤ 3 * Y ^ 2 / a +
      X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 := by
  have HE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 12 * a))
  have HX := mul_le_mul_of_nonneg_left HE (by positivity : 0 ≤ X ^ 2 / (4 * a))
  have HY : 0 ≤ 3 * Y ^ 2 / a * Real.exp (-a * t) := by positivity
  have HN : 0 ≤ a * A / 8 * Real.exp (-2 * t) := by positivity
  dsimp only [shearTailDrift]
  nlinarith only [HX, HY, HN, show 0 ≤ X ^ 2 / (4 * a) by positivity]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTail_prefix {a A X Y T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t))
    (hinit : α 0 2 ≤ A ∧ α 0 3 ≤ X ∧ α 0 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ A * Real.exp (-2 * t) ∧
      α t 3 ≤ X * Real.exp (6 * a * t) ∧
      α t 4 ≤ Y * Real.exp (-(a / 2) * t) ∧
      |α t 1 - α 0 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + α t 0 ∧ 1 + α t 0 ≤ 6 * a ^ 2 ∧ α t 0 ≤ -(15 / 16) := by
  have H (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := hregion t ht
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by linarith only [(H t ht).1]
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_constraint_bounds ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_wall_rates ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      α t 2 ≤ A * Real.exp (-2 * t) ∧ α t 3 ≤ X * Real.exp (6 * a * t) ∧
        α t 4 ≤ Y * Real.exp (-(a / 2) * t) := by
    have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    have HD (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) := hasDerivAt_normalized_components (hα u hu)
    have Hn := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).1 (hn u hu).1) hz ht ht.1
    have Hx := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right ((le_abs_self _).trans (HR u hu).2.1) (hn u hu).2.1) hz ht ht.1
    have Hy := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.2)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).2.2 (hn u hu).2.2) hz ht ht.1
    simp only [sub_zero] at Hn Hx Hy
    rw [neg_div] at Hy
    exact ⟨Hn.trans (mul_le_mul_of_nonneg_right hinit.1 (Real.exp_pos _).le),
      Hx.trans (mul_le_mul_of_nonneg_right hinit.2.1 (Real.exp_pos _).le),
      Hy.trans (mul_le_mul_of_nonneg_right hinit.2.2 (Real.exp_pos _).le)⟩
  have HS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |shearMinus (α t 1) (α t 2) (α t 3) (α t 4)| ≤
        3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
          a * A / 4 * Real.exp (-2 * t) := by
    have Hs := shearTail_shear_rate ⟨ha.1.le, ha.2⟩
      (abs_le.mpr ⟨by linarith only [(H t ht).2.1, ha.1], (H t ht).2.2.1⟩)
      (hn t ht).1 (hn t ht).2.1 (hn t ht).2.2
    have Hx := pow_le_pow_left₀ (hn t ht).2.1 (HW t ht).2.1 2
    have Hy := pow_le_pow_left₀ (hn t ht).2.2 (HW t ht).2.2 2
    have hxsq : (X * Real.exp (6 * a * t)) ^ 2 = X ^ 2 * Real.exp (12 * a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have hysq : (Y * Real.exp (-(a / 2) * t)) ^ 2 = Y ^ 2 * Real.exp (-a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [hxsq] at Hx
    rw [hysq] at Hy
    have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
    have hcoef : 3 * (α t 3 + α t 4 + a * α t 2) ≤ a / 4 := by
      have Han := mul_le_mul_of_nonneg_left (H t ht).2.2.2.1 ha.1.le
      have Haa := mul_le_mul_of_nonneg_left ha2 ha.1.le
      nlinarith only [Han, Haa, ha2, (H t ht).2.2.2.2.1, (H t ht).2.2.2.2.2]
    have Hcoef := mul_le_mul_of_nonneg_right hcoef (hn t ht).1
    have Hn := mul_le_mul_of_nonneg_left (HW t ht).1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 4)
    nlinarith only [Hs, Hx, Hy, Hcoef, Hn]
  have HG := abs_sub_le_of_deriv_primitive
    (fun t ht => (hasDerivAt_normalized_components (hα t ht)).2.1)
    (fun t _ => hasDerivAt_shearTailDrift ha.1.ne' A X Y t) HS
  intro t ht
  obtain ⟨Hn, Hx, Hy⟩ := HW t ht
  obtain ⟨_, _, _, _, Hp, Hl, Hu⟩ := HB t ht
  refine ⟨Hn, Hx, Hy, ?_, Hl, Hu, Hp⟩
  simpa only [shearTailDrift, mul_zero, Real.exp_zero, sub_self, mul_zero, zero_add, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_shearTailRegion (a : ℝ) : IsClosed {z | shearTailRegion a z} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 1)).inter
      ((isClosed_le (continuous_apply 1) continuous_const).inter
        ((isClosed_le (continuous_apply 2) continuous_const).inter
          ((isClosed_le (continuous_apply 3) continuous_const).inter
            (isClosed_le (continuous_apply 4) continuous_const)))))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_shearTail_control {a A X Y T : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hA : 0 ≤ A ∧ A < a ^ 2)
    (hX : 0 ≤ X ∧ X * Real.exp (6 * a * T) < a ^ 2)
    (hY : 0 ≤ Y ∧ Y < a / 16)
    (hc : stateConstraint z = 1) (hp : z 0 < 0)
    (hs : 3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hinit : z 2 ≤ A ∧ z 3 ≤ X ∧ z 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let w := normalizedMaxCurve z 0 t
      t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
      w 2 ≤ A * Real.exp (-2 * t) ∧ w 3 ≤ X * Real.exp (6 * a * t) ∧
      w 4 ≤ Y * Real.exp (-(a / 2) * t) ∧ |w 1 - z 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ w 0 ≤ -(15 / 16) := by
  have hbudget : 3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 ≤ a / 8 := by
    have HY := pow_le_pow_left₀ hY.1 hY.2.le 2
    have HX := pow_le_pow_left₀ (mul_nonneg hX.1 (Real.exp_pos _).le) hX.2.le 2
    have he : (X * Real.exp (6 * a * T)) ^ 2 = X ^ 2 * Real.exp (12 * a * T) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [he] at HX
    have HA := mul_le_mul_of_nonneg_left hA.2.le (sq_nonneg a)
    have haSq : a ^ 2 ≤ 1 / 256 := by nlinarith only [ha.1, ha.2]
    have Haa := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr haSq)
    have hid : a * (3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8) =
        3 * Y ^ 2 + X ^ 2 * Real.exp (12 * a * T) / 4 + a ^ 2 * A / 8 := by
      field_simp [ha.1.ne']
    apply (mul_le_mul_iff_right₀ ha.1).mp
    rw [hid]
    nlinarith only [HY, HX, HA, Haa, sq_nonneg a]
  let α := normalizedMaxCurve z 0
  let S := {t : ℝ | shearTailRegion a (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 :=
    ⟨(normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)).2.mpr hn.1,
      (normalizedMaxCurve_wall_sign hc ht (1 : Fin 3)).2.mpr hn.2.1,
      (normalizedMaxCurve_wall_sign hc ht (2 : Fin 3)).2.mpr hn.2.2⟩
  have hzero : α 0 = z := normalizedMaxCurve_initial z 0
  have hXsmall : X < a ^ 2 := by
    have HE : 1 ≤ Real.exp (6 * a * T) := Real.one_le_exp_iff.mpr (by positivity [ha.1])
    exact (le_mul_of_one_le_right hX.1 HE).trans_lt hX.2
  have hsz : a / 2 ≤ z 1 ∧ z 1 ≤ 3 * a :=
    ⟨by linarith only [hs.1, ha.1], by linarith only [hs.2, ha.1]⟩
  have HB := shearTail_constraint_bounds ha hp hsz ⟨hn.1, hinit.1.trans hA.2.le⟩
    ⟨hn.2.1, hinit.2.1.trans hXsmall.le⟩ ⟨hn.2.2, hinit.2.2.trans hY.2.le⟩ hc
  have hS0 : (0 : ℝ) ∈ S := by
    change shearTailRegion a (α 0)
    rw [hzero]
    exact ⟨by linarith only [HB.2.2.2.2.1], hsz.1, hsz.2,
      hinit.1.trans hA.2.le, hinit.2.1.trans hXsmall.le, hinit.2.2.trans hY.2.le⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_shearTailRegion a)
    convert! H using 1
    ext t
    change (shearTailRegion a (α t) ∧ t ∈ Icc 0 T) ↔ (t ∈ Icc 0 T ∧ shearTailRegion a (α t))
    tauto
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    obtain ⟨Hn, Hx, Hy, Hs, _, _, Hp⟩ := shearTail_prefix ha
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
      (fun u hu => hbefore hu) (by simpa only [hzero] using hinit) t ⟨ht.1, le_rfl⟩
    have HD := Hs.trans ((shearTailDrift_le ha.1 hA.1 ht.2.le).trans hbudget)
    rw [hzero] at HD
    have Hsl : a / 2 < α t 1 := by linarith only [(abs_le.mp HD).1, hs.1, ha.1]
    have Hsu : α t 1 < 3 * a := by linarith only [(abs_le.mp HD).2, hs.2, ha.1]
    have Hnn : α t 2 < a ^ 2 := Hn.trans_lt
      ((mul_le_of_le_one_right hA.1 (Real.exp_le_one_iff.mpr (by linarith only [ht.1]))).trans_lt hA.2)
    have Hxx : α t 3 < a ^ 2 := Hx.trans_lt
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2.le (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hX.2)
    have Hyy : α t 4 < a / 16 := Hy.trans_lt
      ((mul_le_of_le_one_right hY.1 (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith only [ha.1] : -(a / 2) ≤ 0) ht.1))).trans_lt hY.2)
    have Hpp : α t 0 < -(1 / 2) := by linarith only [Hp]
    have Hcont (i : Fin 5) := (continuous_apply i).continuousAt.comp (hα t ht.1).continuousAt
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [(Hcont 0).eventually (isOpen_Iio.mem_nhds Hpp),
        (Hcont 1).eventually (isOpen_Ioi.mem_nhds Hsl),
        (Hcont 1).eventually (isOpen_Iio.mem_nhds Hsu),
        (Hcont 2).eventually (isOpen_Iio.mem_nhds Hnn),
        (Hcont 3).eventually (isOpen_Iio.mem_nhds Hxx),
        (Hcont 4).eventually (isOpen_Iio.mem_nhds Hyy)] with u hu0 hu1 hu2 hu3 hu4 hu5
      exact ⟨hu0.le, hu1.le, hu2.le, hu3.le, hu4.le, hu5.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := shearTail_prefix ha
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
    (fun u hu => hwhole hu) (by simpa only [hzero] using hinit)
  intro t ht
  refine ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1, hwhole ht, ?_⟩
  simpa only [hzero] using H t ht

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
open Set

private theorem BianchiIX.exp_shearTailTime {a : ℝ} (ha : 0 < a) (c D : ℝ) :
    Real.exp (c * a * shearTailTime a D) = a ^ (-c * D) := by
  rw [Real.rpow_def_of_pos ha]
  congr 1
  dsimp only [shearTailTime]
  rw [one_div, Real.log_inv]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearTail_scale_control {h q D P : ℝ}
    (hh : 0 ≤ h) (hq : 2 < q) (hD : 0 ≤ D) (hP : 6 * D + 2 < P) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      ∀ ε ζ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 ≤ ζ ∧ ζ ≤ a ^ P) →
        ∀ z : NormalizedState, stateConstraint z = 1 → z 0 < 0 →
          (3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4) →
          (0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4) →
          (z 2 ≤ h * a ^ q ∧ z 3 ≤ 2 * ζ ∧ z 4 ≤ 4 * ε * a) →
          let T := shearTailTime a D
          0 ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) T,
            let w := normalizedMaxCurve z 0 t
            t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
            w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
            w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
            w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
            |w 1 - z 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
            a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧
            toProjectiveState w 2 < 1 := by
  let C : Fin 2 → ℝ := ![h, 40]
  let p : Fin 2 → ℝ := ![q - 2, P - 6 * D - 2]
  obtain ⟨astar, hastar, hastar', HB⟩ := exists_common_rpow_budget
    (C := C) (p := p) (ε := fun _ => (1 : ℝ) / 2) Finset.univ
    (fun i _ => by fin_cases i; exact hh; norm_num [C])
    (fun i _ => by fin_cases i; dsimp [p]; linarith only [hq]; dsimp [p]; linarith only [hP])
    (fun _ _ => by norm_num) (show (0 : ℝ) < 1 / 256 by norm_num)
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε ζ hε hζ z hc hp hs hn hinit T
  have haSmall : a ≤ 1 / 256 := ha.2.trans hastar'.le
  have HN : h * a ^ (q - 2) < 1 / 2 := HB a ha 0 (Finset.mem_univ _)
  have HX : 40 * a ^ (P - 6 * D - 2) < 1 / 2 := HB a ha 1 (Finset.mem_univ _)
  have hR : 0 ≤ a ^ (P - 6 * D - 2) := Real.rpow_nonneg ha.1.le _
  have hNid : h * a ^ q = (h * a ^ (q - 2)) * a ^ 2 := by
    rw [Real.rpow_sub ha.1, Real.rpow_two]
    field_simp [ha.1.ne']
  have hXid : a ^ P * a ^ (-6 * D) = a ^ (P - 6 * D - 2) * a ^ 2 := by
    rw [← Real.rpow_two a, ← Real.rpow_add ha.1, ← Real.rpow_add ha.1]
    congr 1
    ring
  have hA : 0 ≤ h * a ^ q ∧ h * a ^ q < a ^ 2 := by
    refine ⟨mul_nonneg hh (Real.rpow_nonneg ha.1.le _), ?_⟩
    rw [hNid]
    have H := mul_lt_mul_of_pos_right HN (sq_pos_of_pos ha.1)
    nlinarith only [H, sq_pos_of_pos ha.1]
  have hXtotal : 2 * ζ * Real.exp (6 * a * T) < a ^ 2 / 40 := by
    change 2 * ζ * Real.exp (6 * a * shearTailTime a D) < _
    rw [exp_shearTailTime ha.1 6 D]
    have H := mul_le_mul_of_nonneg_right hζ.2 (Real.rpow_nonneg ha.1.le (-6 * D))
    rw [hXid] at H
    have H' := mul_lt_mul_of_pos_right HX (sq_pos_of_pos ha.1)
    nlinarith only [H, H']
  have hX : 0 ≤ 2 * ζ ∧ 2 * ζ * Real.exp (6 * a * T) < a ^ 2 :=
    ⟨by linarith only [hζ.1], hXtotal.trans (by nlinarith only [sq_pos_of_pos ha.1])⟩
  have hY : 0 ≤ 4 * ε * a ∧ 4 * ε * a < a / 16 := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    exact ⟨mul_nonneg (by linarith only [hε.1]) ha.1.le, by linarith only [H, ha.1]⟩
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [haSmall])))
  have H := normalized_shearTail_control ⟨ha.1, haSmall⟩ hT hA hX hY hc hp hs hn hinit
  refine ⟨hT, ?_⟩
  intro t ht w
  obtain ⟨Hdom, Hreg, Hn, Hx, Hy, Hs, HAl, HAu, _⟩ := H t ht
  have Hdrift := Hs.trans (shearTailDrift_le ha.1 hA.1 ht.2)
  have Hid : 3 * (4 * ε * a) ^ 2 / a + (2 * ζ) ^ 2 / (4 * a) * Real.exp (12 * a * T) +
      a * (h * a ^ q) / 8 = 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 := by
    change _ + _ * Real.exp (12 * a * shearTailTime a D) + _ = _
    rw [exp_shearTailTime ha.1 12 D, Real.rpow_add ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
    ring
  refine ⟨Hdom, Hreg, Hn, Hx, Hy, Hdrift.trans_eq Hid, HAl, HAu, ?_⟩
  have hApos : 0 < 1 + w 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have hx0 : 0 ≤ w 3 := (normalizedMaxCurve_wall_sign hc ht.1 (1 : Fin 3)).2.mpr hn.2.1
  have hxsmall : w 3 < a ^ 2 / 40 := Hx.trans_lt
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hXtotal)
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  change Real.sqrt 3 * w 3 / (1 + w 0) < 1
  apply (div_lt_one hApos).mpr
  have Hr := mul_le_mul_of_nonneg_right hr hx0
  nlinarith only [Hr, hxsmall, HAl, sq_pos_of_pos ha.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projectiveCoordinate_le {a p v B : ℝ}
    (ha : 0 < a) (hA : a ^ 2 / 10 ≤ 1 + p) (hv : 0 ≤ v ∧ v ≤ B) :
    0 ≤ projectiveCoord p v ∧ projectiveCoord p v ≤ 20 * B / a ^ 2 := by
  have hApos : 0 < 1 + p := (div_pos (sq_pos_of_pos ha) (by norm_num)).trans_le hA
  have hB : 0 ≤ B := hv.1.trans hv.2
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hv.1) hApos.le, ?_⟩
  change Real.sqrt 3 * v / (1 + p) ≤ _
  calc
    _ ≤ 2 * B / (a ^ 2 / 10) := div_le_div₀ (by positivity : 0 ≤ 2 * B)
      (mul_le_mul hr hv.2 hv.1 (by norm_num)) (by positivity) hA
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projective_endpoint {a h q D ε ζ : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (hA : a ^ 2 / 10 ≤ 1 + z 0)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hwall : z 2 ≤ h * a ^ q * Real.exp (-2 * shearTailTime a D) ∧
      z 3 ≤ 2 * ζ * Real.exp (6 * a * shearTailTime a D) ∧
      z 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * shearTailTime a D)) :
    0 ≤ toProjectiveState z 1 ∧ toProjectiveState z 1 ≤ 20 * h * a ^ (q - 2) ∧
    0 ≤ toProjectiveState z 2 ∧ toProjectiveState z 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
    0 ≤ toProjectiveState z 3 ∧ toProjectiveState z 3 ≤ 80 * ε * a ^ (D / 2 - 1) := by
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa only [one_mul] using ha.2)))
  have Hn : z 2 ≤ h * a ^ q := hwall.1.trans
    (mul_le_of_le_one_right (mul_nonneg hh (Real.rpow_nonneg ha.1.le _))
      (Real.exp_le_one_iff.mpr (by linarith only [hT])))
  have Hx := hwall.2.1
  rw [exp_shearTailTime ha.1 6 D] at Hx
  have he : Real.exp (-(a / 2) * shearTailTime a D) = a ^ (D / 2) := by
    convert! exp_shearTailTime ha.1 (-(1 / 2)) D using 1 <;> congr 1 <;> ring
  have Hy := hwall.2.2
  rw [he] at Hy
  obtain ⟨Hn0, Hn1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.1, Hn⟩
  obtain ⟨Hx0, Hx1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.1, Hx⟩
  obtain ⟨Hy0, Hy1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.2, Hy⟩
  refine ⟨Hn0, Hn1.trans_eq ?_, Hx0, Hx1.trans_eq ?_, Hy0, Hy1.trans_eq ?_⟩
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
    ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionPhase_eq_core {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hA : 0 < 1 + x 0) :
    restartProjectionPhase (x 2, ![x 1, x 3, x 4]) =
      2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2) := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcore : coreRadius (toProjectiveState x 0) (toProjectiveState x 2) =
      Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) := by
    unfold coreRadius coreEnergy
    change Real.sqrt ((projectiveCoord (x 0) (x 1) - 1) ^ 2 +
      projectiveCoord (x 0) (x 3) ^ 2) = _
    have hid : (projectiveCoord (x 0) (x 1) - 1) ^ 2 + projectiveCoord (x 0) (x 3) ^ 2 =
        ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) ^ 2 := by
      unfold projectiveCoord
      field_simp
      nlinarith only [hsqrt]
    rw [hid, Real.sqrt_div (by positivity), Real.sqrt_sq hA.le]
  rw [restartProjectionPhase, restartProjectionHeight_of_constraint hc hp, hcore]
  change 2 * (1 + x 0) / Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * x 3 ^ 2) = _
  rw [div_div_eq_mul_div]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionPhase_eq_core {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0)
    (hheight : 0 < 1 + normalizedMaxCurve (restartSectionChart h Z) 0 T 0) :
    (fun W => restartProjectionPhase (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => let x := normalizedMaxCurve (restartSectionChart h W) 0 T
        2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2)) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  have HnearR := HR.eventually (isOpen_Ioi.mem_nhds hrad)
  have HnearN := Hcoord.eventually (isOpen_Iio.mem_nhds hneg)
  have HnearA := (continuousAt_const.add Hcoord).eventually (isOpen_Ioi.mem_nhds hheight)
  filter_upwards [HnearR, HnearN, HnearA] with W hW hN hA
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionPhase_eq_core HC hN hA

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_scaled (p : RestartProjectionParameters) :
    restartProjectionDefect (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledDefect p := by
  unfold restartProjectionDefect restartProjectionScaledState restartProjectionScaledDefect curvature
  dsimp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_scaled (p : RestartProjectionParameters) :
    restartProjectionHeight (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledHeight p := by
  rw [restartProjectionHeight, restartProjectionDefect_scaled]
  unfold restartProjectionScaledHeight
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionPhase_scaled {p : RestartProjectionParameters} (hr : 0 < p.1 0) :
    restartProjectionPhase (restartProjectionScaledState p) -
      restartRadialPhase (restartProjectionScaledState p).2 =
        p.1 0 * restartProjectionScaledError p := by
  have hden : (Real.sqrt 3 * (restartProjectionScaledState p).2 0 -
      restartProjectionHeight (restartProjectionScaledState p)) ^ 2 +
      3 * ((restartProjectionScaledState p).2 1) ^ 2 =
        (p.1 0) ^ 2 * restartProjectionScaledDenom p := by
    rw [restartProjectionHeight_scaled]
    dsimp only [restartProjectionScaledState, restartProjectionScaledDenom]
    change (Real.sqrt 3 * (p.1 0 * p.2 0) - (p.1 0) ^ 2 * restartProjectionScaledHeight p) ^ 2 +
      3 * (p.1 0 * p.2 1) ^ 2 = _
    ring
  have hrad : restartRadialNorm (restartProjectionScaledState p).2 =
      p.1 0 * Real.sqrt ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) := by
    unfold restartRadialNorm
    change Real.sqrt ((p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2) = _
    rw [show (p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2 =
      (p.1 0) ^ 2 * ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
  rw [restartProjectionPhase, hden, restartProjectionHeight_scaled,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le, restartRadialPhase, hrad]
  unfold restartProjectionScaledError
  rw [show 2 * (p.1 0 ^ 2 * restartProjectionScaledHeight p) =
    p.1 0 * (p.1 0 * (2 * restartProjectionScaledHeight p)) by ring,
    mul_div_mul_left _ _ hr.ne']
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionScaledError_axis (X : RestartProjectionCenter) :
    restartProjectionScaledError (0, X) = 0 := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hden : restartProjectionScaledDenom (0, X) = 3 * ((X 0) ^ 2 + (X 1) ^ 2) := by
    simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero, mul_pow, hsqrt]
    ring
  have hheight : restartProjectionScaledHeight (0, X) = ((X 0) ^ 2 + (X 1) ^ 2) / 2 := by
    norm_num [restartProjectionScaledHeight, restartProjectionScaledDefect, curvature]
  rw [restartProjectionScaledError, hden, hheight, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [Pi.zero_apply, sub_zero]
  let R := Real.sqrt ((X 0) ^ 2 + (X 1) ^ 2)
  have hR : R ^ 2 = (X 0) ^ 2 + (X 1) ^ 2 := Real.sq_sqrt (by positivity)
  change 2 * (((X 0) ^ 2 + (X 1) ^ 2) / 2) / (Real.sqrt 3 * R) - R / Real.sqrt 3 = 0
  rw [← hR]
  by_cases hR0 : R = 0
  · simp [hR0]
  · have h3 : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartProjectionScaledError {p : RestartProjectionParameters}
    (hr : 0 < 1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p)
    (hd : 0 < restartProjectionScaledDenom p)
    (hv : 0 < (p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError p := by
  have HD : ContDiffAt ℝ k restartProjectionScaledDefect p := by
    unfold restartProjectionScaledDefect curvature
    fun_prop
  have HR : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      1 - (q.1 0) ^ 2 * restartProjectionScaledDefect q) p := by fun_prop
  have HA : ContDiffAt ℝ k restartProjectionScaledHeight p := by
    apply HD.div ((contDiffAt_const).add (HR.sqrt hr.ne'))
    exact ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p))
  have Hden : ContDiffAt ℝ k restartProjectionScaledDenom p := by
    unfold restartProjectionScaledDenom
    fun_prop
  apply ((contDiffAt_const.mul HA).div (Hden.sqrt hd.ne') (ne_of_gt (Real.sqrt_pos.mpr hd))).sub
  have HV : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      (q.2 0) ^ 2 + (q.2 1 - q.1 2) ^ 2) p := by fun_prop
  exact (HV.sqrt hv.ne').div_const _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartProjectionScaledError_direction_bound {u du : RestartProjectionNormal}
    {X dX : RestartProjectionCenter} {C : ℝ}
    (HD : ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C)
    (HT : ∀ w : RestartProjectionCenter,
      |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖) :
    |fderiv ℝ restartProjectionScaledError (u, X) (du, dX)| ≤ C * ‖du‖ + C * ‖u‖ * ‖dX‖ := by
  have HN : |fderiv ℝ restartProjectionScaledError (u, X) (du, 0)| ≤ C * ‖du‖ := by
    have H := ((fderiv ℝ restartProjectionScaledError (u, X)).le_opNorm (du, 0)).trans
      (mul_le_mul_of_nonneg_right HD (norm_nonneg (du, (0 : RestartProjectionCenter))))
    simpa only [Real.norm_eq_abs, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg du)] using H
  have heq : (du, dX) = (du, (0 : RestartProjectionCenter)) + ((0 : RestartProjectionNormal), dX) := by simp
  rw [heq, map_add]
  exact (abs_add_le _ _).trans (add_le_add HN (HT dX))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionScaledState_parameters {r : ℝ} (hr : r ≠ 0) (p : RestartRadialState) :
    restartProjectionScaledState (restartProjectionParametersAt r p) = p := by
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · ext i
    fin_cases i <;> change r * (_ / r) = _ <;> field_simp <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionError_rescaled {r : ℝ} (hr : 0 < r) (p : RestartRadialState) :
    restartProjectionError p = r * restartProjectionScaledError (restartProjectionParametersAt r p) := by
  have H := restartProjectionPhase_scaled (p := restartProjectionParametersAt r p) hr
  rw [restartProjectionScaledState_parameters hr.ne'] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_restartProjectionParametersAt (r : ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (restartProjectionParametersAt r) := by
  unfold restartProjectionParametersAt
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ k (fun _ : RestartRadialState => r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.1 / r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 2 / r)
      fun_prop
  · apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 0 / r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 1 / r)
      fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartProjectionParametersAt {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {t : ℝ} (H : HasDerivAt p v t) (r : ℝ) :
    HasDerivAt (fun s => restartProjectionParametersAt r (p s)) (restartProjectionParameterTangent r v) t := by
  have Hfst : HasDerivAt (fun s => (p s).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hsnd : HasDerivAt (fun s => (p s).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have HN : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).1)
      (restartProjectionParameterTangent r v).1 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_const t r using 1
    · convert! Hfst.div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 2).div_const r using 1
  have HC : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).2)
      (restartProjectionParameterTangent r v).2 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! (hasDerivAt_pi.mp Hsnd 0).div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 1).div_const r using 1
  exact HN.prodMk HC

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartProjectionError {r : ℝ} {p : RestartRadialState} (hr : 0 < r)
    (H : ContDiffAt ℝ 2 restartProjectionScaledError (restartProjectionParametersAt r p)) :
    ContDiffAt ℝ 2 restartProjectionError p := by
  have heq : restartProjectionError = fun q => r * restartProjectionScaledError (restartProjectionParametersAt r q) :=
    funext (restartProjectionError_rescaled hr)
  rw [heq]
  exact contDiffAt_const.mul (H.comp p (contDiff_restartProjectionParametersAt r 2).contDiffAt)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartProjectionError {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {r t : ℝ} (hr : 0 < r) (Hp : HasDerivAt p v t)
    (H : DifferentiableAt ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))) :
    HasDerivAt (fun s => restartProjectionError (p s))
      (r * fderiv ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))
        (restartProjectionParameterTangent r v)) t := by
  have HD := (H.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_restartProjectionParametersAt Hp r)).const_mul r
  simpa only [Function.comp_apply, restartProjectionError_rescaled hr] using HD

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_restartProjectionScaledError_shear_axis {X : RestartProjectionCenter}
    (hs : X 0 ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError (0, X) := by
  apply contDiffAt_restartProjectionScaledError
  · simp
  · simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith only [sq_pos_of_ne_zero hs, sq_nonneg (X 1)]
  · simp only [Pi.zero_apply, sub_zero]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearRestartProjectionScaledError_bounds {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ X : RestartProjectionCenter, c ≤ |X 0| → |X 0| ≤ M → |X 1| ≤ M →
        ∀ u : RestartProjectionNormal, ‖u‖ ≤ δ →
          ContDiffAt ℝ 2 restartProjectionScaledError (u, X) ∧
          |restartProjectionScaledError (u, X)| ≤ C * ‖u‖ ∧
          ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C ∧
          ∀ w : RestartProjectionCenter,
            |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖ := by
  let K : Set RestartProjectionCenter := Metric.closedBall 0 M ∩ {X | c ≤ |X 0|}
  have hK : IsCompact K := (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const ((continuous_apply 0).abs))
  have hreg (X : RestartProjectionCenter) (hX : X ∈ K) :
      ContDiffAt ℝ 2 restartProjectionScaledError (0, X) := by
    apply contDiffAt_restartProjectionScaledError_shear_axis
    have H : 0 < |X 0| := hc.trans_le hX.2
    exact abs_pos.mp H
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_vanishing_slice_bounds hK hreg restartProjectionScaledError_axis
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro X hXlo hX₀ hX₁ u hu
  have hX : X ∈ K := by
    refine ⟨?_, hXlo⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg ((abs_nonneg (X 0)).trans hX₀)).mpr
    intro i
    fin_cases i
    · exact hX₀
    · exact hX₁
  exact H X hX u hu

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearRestartProjectionError_quadratic :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ a ∈ Ioc (0 : ℝ) δ,
      ∀ (p : ℝ → RestartRadialState) (v : RestartRadialState) (t B : ℝ),
        HasDerivAt p v t → 0 ≤ B →
        a / 2 ≤ |(p t).2 0| → |(p t).2 0| ≤ 4 * a → |(p t).2 1| ≤ 4 * a →
        |(p t).1| ≤ a ^ 2 → |(p t).2 2| ≤ a ^ 2 →
        |v.2 0| ≤ B → |v.2 1| ≤ B → |v.1| ≤ B * a → |v.2 2| ≤ B * a →
          ContDiffAt ℝ 2 restartProjectionError (p t) ∧
          DifferentiableAt ℝ (fun r => restartProjectionError (p r)) t ∧
          |restartProjectionError (p t)| ≤ C * a ^ 2 ∧
          |deriv (fun r => restartProjectionError (p r)) t| ≤ 2 * C * B * a := by
  obtain ⟨δ, hδ, C, hC, HC⟩ := exists_shearRestartProjectionScaledError_bounds
    (c := 1 / 2) (M := 4) (by norm_num)
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro a ha p v t B Hp hB hslo hshi hx hn hy hvs hvx hvn hvy
  have ha0 := ha.1.le
  let u := (restartProjectionParametersAt a (p t)).1
  let X := (restartProjectionParametersAt a (p t)).2
  let du := (restartProjectionParameterTangent a v).1
  let dX := (restartProjectionParameterTangent a v).2
  have hu : ‖u‖ ≤ a := by
    apply (pi_norm_le_iff_of_nonneg ha.1.le).mpr
    intro i
    fin_cases i
    · exact le_of_eq (abs_of_pos ha.1)
    · change |(p t).1 / a| ≤ a
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (by nlinarith only [hn])
    · change |(p t).2 2 / a| ≤ a
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (by nlinarith only [hy])
  have hXlo : 1 / 2 ≤ |X 0| := by
    change 1 / 2 ≤ |(p t).2 0 / a|
    rw [abs_div, abs_of_pos ha.1]
    exact (le_div_iff₀ ha.1).mpr (by linarith only [hslo])
  have hXhi : |X 0| ≤ 4 := by
    change |(p t).2 0 / a| ≤ 4
    rw [abs_div, abs_of_pos ha.1]
    exact (div_le_iff₀ ha.1).mpr hshi
  have hXwall : |X 1| ≤ 4 := by
    change |(p t).2 1 / a| ≤ 4
    rw [abs_div, abs_of_pos ha.1]
    exact (div_le_iff₀ ha.1).mpr hx
  have H := HC X hXlo hXhi hXwall u (hu.trans ha.2)
  have hdu : ‖du‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    fin_cases i
    · change |(0 : ℝ)| ≤ B
      simpa only [abs_zero] using hB
    · change |v.1 / a| ≤ B
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr hvn
    · change |v.2 2 / a| ≤ B
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr hvy
  have hdX : ‖dX‖ ≤ B / a := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hB ha.1.le)).mpr
    intro i
    fin_cases i
    · change |v.2 0 / a| ≤ B / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right hvs ha.1.le
    · change |v.2 1 / a| ≤ B / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right hvx ha.1.le
  have HD := hasDerivAt_restartProjectionError ha.1 Hp (H.1.differentiableAt (by norm_num))
  have Hdir := restartProjectionScaledError_direction_bound (du := du) (dX := dX) H.2.2.1 H.2.2.2
  have hC0 : 0 ≤ C := by linarith only [hC]
  refine ⟨contDiffAt_restartProjectionError ha.1 H.1, HD.differentiableAt, ?_, ?_⟩
  · rw [restartProjectionError_rescaled ha.1, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (C * ‖u‖) := mul_le_mul_of_nonneg_left H.2.1 ha.1.le
      _ ≤ a * (C * a) := by gcongr
      _ = C * a ^ 2 := by ring
  · rw [HD.deriv, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (C * ‖du‖ + C * ‖u‖ * ‖dX‖) := mul_le_mul_of_nonneg_left Hdir ha.1.le
      _ ≤ a * (C * B + C * a * (B / a)) := by gcongr
      _ = 2 * C * B * a := by field_simp [ha.1.ne']; ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_control :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 ≤ ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 ≤ ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Z := restartShearCurve 1 ζ ν ρ
            let t₀ := q / 2 * Real.log (1 / a)
            let T := shearTailTime a D
            let x := restartSectionChart h Z
            let y := normalizedMaxCurve x 0 t₀
            a ≤ 1 ∧ 0 ≤ t₀ ∧ 0 ≤ T ∧ 0 < restartSectionRadicand h Z ∧ stateConstraint x = 1 ∧
            (∀ t ∈ Icc (0 : ℝ) T,
              let w := restartShearTailFlow h a q ζ ν t ρ
              t + t₀ ∈ normalizedMaxDomain x 0 ∧ w = normalizedMaxCurve y 0 t ∧
              stateConstraint w = 1 ∧ (0 ≤ w 2 ∧ 0 ≤ w 3 ∧ 0 ≤ w 4) ∧
              shearTailRegion a w ∧ w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
              w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
              w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
              |w 1 - y 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
              a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ toProjectiveState w 2 < 1) ∧
            (let w := restartShearTailFlow h a q ζ ν T ρ;
              toProjectiveState w 1 ≤ 20 * h * a ^ (q - 2) ∧
              toProjectiveState w 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
              toProjectiveState w 3 ≤ 80 * ε * a ^ (D / 2 - 1)) := by
  obtain ⟨C, _, hstar, hhstar, HF⟩ := exists_restartShearFastEntry_control
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aF, haF, HFa⟩ := HF h hh q hq
  obtain ⟨aT, haT, HTa⟩ := exists_shearTail_scale_control hh.1.le hq hD hP
  refine ⟨min aF aT, lt_min haF haT, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Z t₀ T x y
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨ha1, _, ht₀, hrad, hdom, hcy, hpy, _, hnpos, hnhi, hsy, _, _, _, HW⟩ :=
    HFa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε 1 ζ ν hε' (by norm_num)
      ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  have hcx : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hn : 0 ≤ y 2 ∧ y 2 ≤ h * a ^ q := ⟨hnpos.le, hnhi⟩
  have Hx : 0 ≤ y 3 ∧ y 3 ≤ 2 * ζ := by
    have H := HW 0
    change ζ / 2 ≤ y 3 ∧ y 3 ≤ 2 * ζ ∧ _ at H
    exact ⟨by linarith only [H.1, hζ.1], H.2.1⟩
  have Hy : 0 ≤ y 4 ∧ y 4 ≤ 4 * ε * a := by
    have H := HW 1
    change ν / 2 ≤ y 4 ∧ y 4 ≤ 2 * ν ∧ _ at H
    exact ⟨by linarith only [H.1, hν.1], by linarith only [H.2.1, hν.2]⟩
  have HS : 3 * a / 4 ≤ y 1 ∧ y 1 ≤ 9 * a / 4 := by
    change 3 * a / 4 ≤ 1 * y 1 ∧ 1 * y 1 ≤ 9 * a / 4 at hsy
    simpa only [one_mul] using hsy
  obtain ⟨hT, HT⟩ := HTa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ hε
    ⟨hζ.1, hζ.2.1⟩ y hcy (by linarith only [hpy]) HS ⟨Hn.1, Hx.1, Hy.1⟩ ⟨Hn.2, Hx.2, Hy.2⟩
  have Hall (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      t + t₀ ∈ normalizedMaxDomain x 0 ∧
      restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t ∧
      stateConstraint (restartShearTailFlow h a q ζ ν t ρ) = 1 ∧
      (0 ≤ restartShearTailFlow h a q ζ ν t ρ 2 ∧
        0 ≤ restartShearTailFlow h a q ζ ν t ρ 3 ∧ 0 ≤ restartShearTailFlow h a q ζ ν t ρ 4) := by
    have htime : 0 ≤ t + t₀ := add_nonneg ht.1 ht₀
    have htot := normalizedMaxDomain_contains_Ici_of_constraint hcx 0 htime
    have Heq : restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t := by
      change normalizedMaxCurve x 0 (t + t₀) = normalizedMaxCurve (normalizedMaxCurve x 0 t₀) 0 t
      simpa only [zero_add] using
        (normalizedMaxCurve_shift (by simpa only [zero_add] using hdom) htot).symm
    refine ⟨htot, Heq, (normalizedMaxCurve_forward_of_constraint hcx htime).2.1, ?_⟩
    rw [Heq]
    exact ⟨(normalizedMaxCurve_wall_sign hcy ht.1 (0 : Fin 3)).2.mpr Hn.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (1 : Fin 3)).2.mpr Hx.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (2 : Fin 3)).2.mpr Hy.1⟩
  refine ⟨ha1, ht₀, hT, hrad, hcx, ?_, ?_⟩
  · intro t ht w
    obtain ⟨Hdom, Heq, Hc, Hpos⟩ := Hall t ht
    refine ⟨Hdom, Heq, Hc, Hpos, ?_⟩
    change w = normalizedMaxCurve y 0 t at Heq
    rw [Heq]
    exact (HT t ht).2
  · have heq := (Hall T ⟨hT, le_rfl⟩).2.1
    obtain ⟨_, _, HnT, HxT, HyT, _, HAl, _, _⟩ := HT T ⟨hT, le_rfl⟩
    have Hpos := (Hall T ⟨hT, le_rfl⟩).2.2.2
    rw [heq] at Hpos ⊢
    have Hproj := shearTail_projective_endpoint ⟨ha.1, ha1⟩ hh.1.le hD HAl Hpos ⟨HnT, HxT, HyT⟩
    exact ⟨Hproj.2.1, Hproj.2.2.2.1, Hproj.2.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_endpoint_control :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let z := restartShearTailFlow h a q ζ ν T ρ
            let v := restartShearTailRadialVariation h a q ζ ν T ρ
            let B := 13 + 16 * C * q + 40 * D
            a ≤ 1 / 256 ∧ 0 ≤ T + q / 2 * Real.log (1 / a) ∧
            0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ) ∧
            T + q / 2 * Real.log (1 / a) ∈
              normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
            stateConstraint z = 1 ∧ positiveWalls z ∧ shearTailRegion a z ∧ 0 < 1 + z 0 ∧
            HasDerivAt (restartShearTailFlow h a q ζ ν T) v ρ ∧
            |z 2| ≤ a ^ 2 ∧ |z 4| ≤ a ^ 2 ∧
            |v 1| ≤ B ∧ |v 3| ≤ B ∧ |v 2| ≤ B * a ∧ |v 4| ≤ B * a := by
  obtain ⟨C, hC, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨C, hC, min hR (min hV 1), lt_min hhR (lt_min hhV (by norm_num)), ?_⟩
  intro h hh q D P hq hD hP
  have hD0 : 0 ≤ D := by linarith only [hD]
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD0 hP
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D P hq hD0 hP
  obtain ⟨an, han, HAn⟩ := exists_rpow_log_quadratic_scale hq
  obtain ⟨ay, hay, HAy⟩ := exists_rpow_log_quadratic_scale (show 2 < D / 2 + 1 by linarith only [hD])
  refine ⟨min aR (min aV (min an ay)), lt_min haR (lt_min haV (lt_min han hay)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T z v B
  obtain ⟨hasmall, hT, _, _, _, _, _, _, HRT⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, ht₀, _, hrad, _, HVT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  obtain ⟨ha1, Hnsmall, Hnlog⟩ := HAn a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  obtain ⟨_, Hysmall, Hylog⟩ := HAy a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨HD, Hpos, HS, _, HL⟩ := HRT T ⟨hT, le_rfl⟩
  obtain ⟨Hdom, _, Hcon, Hnon, Hreg, Hn, _, Hy, _, HA, _⟩ := HVT T ⟨hT, le_rfl⟩
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have ha0 := ha.1.le
  have hh1 : h ≤ 1 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have Hnpow : z 2 ≤ a ^ q := Hn.trans
    ((mul_le_of_le_one_right (by positivity [hh.1] : 0 ≤ h * a ^ q)
      (Real.exp_le_one_iff.mpr (by linarith only [hT]))).trans
      (mul_le_of_le_one_left (Real.rpow_nonneg ha0 _) hh1))
  have he : Real.exp (-(a / 2) * T) = a ^ (D / 2) := by
    convert! exp_shearTailTime ha.1 (-(1 / 2)) D using 1 <;> congr 1 <;> ring
  have Hypow : z 4 ≤ a ^ (D / 2 + 1) := by
    rw [he] at Hy
    have Heps : 4 * ε ≤ 1 := by linarith only [hε.2]
    have H := mul_le_mul_of_nonneg_right Heps (by positivity [ha.1] : 0 ≤ a * a ^ (D / 2))
    rw [Real.rpow_add ha.1, Real.rpow_one]
    nlinarith only [Hy, H]
  let L := shearTailLogSize z v
  let K := 4 + 8 * C * q + 20 * D
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hKB : K ≤ B := by dsimp only [K, B]; nlinarith only [mul_nonneg hC0 hq0, hD0]
  have htime : a * T = D * |Real.log a| := by
    dsimp only [T, shearTailTime]
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) ha.1.ne', Real.log_one, zero_sub,
      abs_of_nonpos (Real.log_nonpos ha0 ha1)]
    field_simp [ha.1.ne']
  have HLa : a * L ≤ K * (1 + |Real.log a|) := by
    have H := mul_le_mul_of_nonneg_left HL ha0
    have Hs := mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ 8 * C * q * |Real.log a|)
    have Ht := mul_nonneg hD0 (abs_nonneg (Real.log a))
    dsimp only [K]
    change a * shearTailLogSize z v ≤ _
    nlinarith only [H, Hs, htime, ha1, mul_nonneg hC0 hq0, hD0, abs_nonneg (Real.log a)]
  have HW (i : Fin 3) (hi : 0 < z (i.addNat 2)) : |v (i.addNat 2)| ≤ z (i.addNat 2) * L := by
    have H := norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at H
    simpa only [L, shearTailLogSize, mul_comm] using (div_le_iff₀ hi).mp H
  have Hnormal (i : Fin 3) (hi : 0 < z (i.addNat 2)) (p : ℝ)
      (hpow : z (i.addNat 2) ≤ a ^ p) (hlog : a ^ p * (1 + |Real.log a|) ≤ a ^ 2) :
      |v (i.addNat 2)| ≤ B * a := by
    have H0 := mul_le_mul_of_nonneg_left (HW i hi) ha0
    have H1 := mul_le_mul_of_nonneg_left HLa hi.le
    have H2 := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ K * (1 + |Real.log a|))
    have H3 := mul_le_mul_of_nonneg_left hlog hK
    have H4 := mul_le_mul_of_nonneg_right hKB (sq_nonneg a)
    apply (mul_le_mul_iff_left₀ ha.1).mp
    nlinarith only [H0, H1, H2, H3, H4]
  have hlogsmall : a * |Real.log a| ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ha.1) ha0
    rw [mul_sub, mul_one, mul_inv_cancel₀ ha.1.ne'] at H
    rw [abs_of_nonpos (Real.log_nonpos ha0 ha1)]
    nlinarith only [H, ha.1]
  have Hx : |v 3| ≤ B := by
    have H0 := mul_le_mul_of_nonneg_left (HW 1 Hpos.2.1) ha0
    change a * |v 3| ≤ a * (z 3 * L) at H0
    have H1 := mul_le_mul_of_nonneg_left HLa Hpos.2.1.le
    change z 3 * (a * L) ≤ z 3 * (K * (1 + |Real.log a|)) at H1
    have H2 := mul_le_mul_of_nonneg_right Hreg.2.2.2.2.1
      (by positivity : 0 ≤ K * (1 + |Real.log a|))
    change z 3 * (K * (1 + |Real.log a|)) ≤ a ^ 2 * (K * (1 + |Real.log a|)) at H2
    have Hsmall : a * (1 + |Real.log a|) ≤ 2 := by linarith only [ha1, hlogsmall]
    have H3 := mul_le_mul_of_nonneg_left Hsmall (mul_nonneg ha0 hK)
    have H4 : 2 * K ≤ B := by dsimp only [K, B]; ring_nf; linarith
    have H5 := mul_le_mul_of_nonneg_left H4 ha0
    apply (mul_le_mul_iff_left₀ ha.1).mp
    nlinarith only [H0, H1, H2, H3, H5]
  refine ⟨hasmall, add_nonneg hT ht₀, hrad, Hdom, Hcon, Hpos, Hreg,
    (by nlinarith only [HA, sq_pos_of_pos ha.1]), HD, ?_, ?_, ?_, Hx,
    Hnormal 0 Hpos.1 q Hnpow Hnlog, Hnormal 2 Hpos.2.2 (D / 2 + 1) Hypow Hylog⟩
  · rw [abs_of_pos Hpos.1]
    exact Hnpow.trans Hnsmall
  · rw [abs_of_pos Hpos.2.2]
    exact Hypow.trans Hysmall
  · exact HS.trans (by dsimp only [B]; nlinarith only [mul_nonneg hC0 hq0, hD0])

end
end

/-- The instantaneous growing-circle phase and the physical radius agree to first radial order. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ K > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let E := fun r => restartShearTailProjectionPhase h a q ζ ν T r -
              restartShearTailPhase h a q ζ ν T r
            T + q / 2 * Real.log (1 / a) ∈
              normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
            0 < 1 + restartShearTailFlow h a q ζ ν T ρ 0 ∧
            DifferentiableAt ℝ E ρ ∧ |E ρ| ≤ K * a ^ 2 ∧ |deriv E ρ| ≤ K * a := by
  obtain ⟨C, hC, hstar, hhstar, H⟩ := exists_restartShearTail_endpoint_control
  obtain ⟨δ, hδ, CE, hCE, HE⟩ := exists_shearRestartProjectionError_quadratic
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D hq hD
  let B := 13 + 16 * C * q + 40 * D
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hB : 1 ≤ B := by dsimp only [B]; nlinarith only [mul_nonneg hC0 hq0, hD0]
  have hCE0 : 0 < CE := by linarith only [hCE]
  let K := 2 * CE * B
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro P hP
  obtain ⟨a₀, ha₀, HA⟩ := H h hh q D P hq hD hP
  refine ⟨min a₀ δ, lt_min ha₀ hδ, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T E
  let z := restartShearTailFlow h a q ζ ν T ρ
  let v := restartShearTailRadialVariation h a q ζ ν T ρ
  let τ := T + q / 2 * Real.log (1 / a)
  let R := fun r => restartSectionRadialState h τ (restartShearCurve 1 ζ ν r)
  let vR : RestartRadialState := (v 2, restartCenterProjection v)
  obtain ⟨hasmall, hτ, hrad, Hdom, _, Hpos, Hreg, Hheight, HD, Hn, Hy, HS, HX, HN, HY⟩ :=
    HA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  have HR : HasDerivAt R vR ρ :=
    (hasDerivAt_pi.mp HD 2).prodMk (restartCenterProjection.hasFDerivAt.comp_hasDerivAt ρ HD)
  have hs : 0 < z 1 := by linarith only [Hreg.2.1, ha.1]
  have hslo : a / 2 ≤ |(R ρ).2 0| := by
    change a / 2 ≤ |z 1|
    rw [abs_of_pos hs]
    exact Hreg.2.1
  have hshi : |(R ρ).2 0| ≤ 4 * a := by
    change |z 1| ≤ 4 * a
    rw [abs_of_pos hs]
    linarith only [Hreg.2.2.1, ha.1]
  have hx : |(R ρ).2 1| ≤ 4 * a := by
    change |z 3| ≤ 4 * a
    rw [abs_of_pos Hpos.2.1]
    nlinarith only [Hreg.2.2.2.2.1, hasmall, ha.1]
  obtain ⟨_, HED, HEv, HEd⟩ := HE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ R vR ρ B HR
    (by linarith only [hB]) hslo hshi hx Hn Hy HS HX HN HY
  have hneg : z 0 < 0 := by linarith only [Hreg.1]
  have Hgerm := (eventually_restartSectionProjectionPhase_eq_core hrad hτ
    hneg Hheight).comp_tendsto
    (hasDerivAt_restartShearCurve 1 ζ ν ρ).continuousAt
  have Hlocal : E =ᶠ[𝓝 ρ] (fun r => restartProjectionError (R r)) := by
    filter_upwards [Hgerm] with r hr
    change restartProjectionPhase (R r) = restartShearTailProjectionPhase h a q ζ ν T r at hr
    change restartShearTailProjectionPhase h a q ζ ν T r - restartRadialPhase (R r).2 =
      restartProjectionPhase (R r) - restartRadialPhase (R r).2
    rw [hr]
  have HEder : HasDerivAt E (deriv (fun r => restartProjectionError (R r)) ρ) ρ :=
    HED.hasDerivAt.congr_of_eventuallyEq Hlocal
  have hCEK : CE ≤ K := by
    dsimp only [K]
    nlinarith only [mul_le_mul_of_nonneg_left hB hCE0.le, hCE0]
  refine ⟨Hdom, Hheight, HEder.differentiableAt, ?_, ?_⟩
  · rw [Hlocal.eq_of_nhds]
    exact HEv.trans (mul_le_mul_of_nonneg_right hCEK (sq_nonneg a))
  · rw [HEder.deriv]
    exact HEd
