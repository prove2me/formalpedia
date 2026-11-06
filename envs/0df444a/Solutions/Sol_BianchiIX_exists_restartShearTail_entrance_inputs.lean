-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_entrance_inputs
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:53:22.250167+00:00
-- url     : https://prove2.me/submissions/fc6eff36-bfcc-47f7-b460-da08a7346fbe

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_RadialTransportData
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_exists_restartShearTail_radial_control
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveCoord
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_normalizedConstraintDifferential_flow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_shearTail_constraint_bounds
import Theorems.Thm_BianchiIX_toProjectiveState_positive
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

noncomputable section
open BianchiIX
open Set

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
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_shearTail_entrance_wall_scale {h q D δ : ℝ}
    (hq : 2 < q) (hD : 2 < D) (hδ : 0 < δ) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) * (1 + |Real.log a|) ≤ δ := by
  have Hp (p : ℝ) (hp : 0 < p) :
      Tendsto (fun a : ℝ => a ^ p + |Real.log a * a ^ p|) (𝓝[>] 0) (𝓝 0) := by
    have H : Tendsto (fun a : ℝ => a ^ p) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hp.ne'] using
        (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [abs_zero, add_zero] using H.add (tendsto_log_mul_rpow_nhdsGT_zero hp).abs
  have Hn := Hp (q - 2) (by linarith only [hq])
  have Hy := Hp (D / 2 - 1) (by linarith only [hD])
  have H : Tendsto (fun a : ℝ => 20 * h * (a ^ (q - 2) + |Real.log a * a ^ (q - 2)|) +
      80 * (a ^ (D / 2 - 1) + |Real.log a * a ^ (D / 2 - 1)|)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (Hn.const_mul (20 * h)).add (Hy.const_mul 80)
  have HI : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HE : ∀ᶠ a : ℝ in 𝓝[>] 0,
      a ≤ 1 ∧ (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) * (1 + |Real.log a|) ≤ δ := by
    filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from self_mem_nhdsWithin,
      HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      H.eventually (gt_mem_nhds hδ)] with a ha ha1 hb
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le (q - 2)),
      abs_of_nonneg (Real.rpow_nonneg ha.le (D / 2 - 1))] at hb
    exact ⟨ha1.le, by nlinarith only [hb]⟩
  obtain ⟨astar, hastar, HA⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp HE
  exact ⟨astar, hastar, fun a ha => HA ha⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_le_abs_add (a b : ℝ) : phaseNorm a b ≤ |a| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hs := phaseNorm_sq a b
  nlinarith only [hr, hs, sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTail_polynomials {α : ℝ → NormalizedState} {v : NormalizedState} {t : ℝ}
    (hα : HasDerivAt α v t) :
    HasDerivAt (fun u => curvature (α u 2) (α u 3) (α u 4)) (shearTailCurvatureDifferential (α t) v) t ∧
    HasDerivAt (fun u => -(α u 3) ^ 2 + (α u 4) ^ 2 + α u 2 * α u 3 - α u 2 * α u 4)
      (shearTailCouplingDifferential (α t) v) t := by
  have hn := hasDerivAt_pi.mp hα 2
  have hx := hasDerivAt_pi.mp hα 3
  have hy := hasDerivAt_pi.mp hα 4
  constructor
  · convert! (((hn.pow 2).add (hx.pow 2)).add (hy.pow 2)).sub
      ((((hn.mul hx).add (hx.mul hy)).add (hy.mul hn)).const_mul 2) using 1
    dsimp only [shearTailCurvatureDifferential]
    ring
  · convert! ((((hx.pow 2).neg.add (hy.pow 2)).add (hn.mul hx)).sub (hn.mul hy)) using 1
    dsimp only [shearTailCouplingDifferential]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedConstraintDifferential_shearTail (z v : NormalizedState) :
    normalizedConstraintDifferential z v = 2 * z 0 * v 0 + 2 * z 1 * v 1 +
      shearTailCurvatureDifferential z v := by
  let α : ℝ → NormalizedState := fun t i => z i + t * v i
  have hα : HasDerivAt α v 0 := hasDerivAt_pi.mpr (fun i => by
    simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (v i)).const_add (z i))
  have hz : α 0 = z := by ext i; simp [α]
  have H := (hasFDerivAt_stateConstraint (α 0)).comp_hasDerivAt 0 hα
  have HQ := (hasDerivAt_shearTail_polynomials hα).1
  have H' := (((hasDerivAt_pi.mp hα 0).pow 2).add ((hasDerivAt_pi.mp hα 1).pow 2)).add HQ
  change HasDerivAt (fun t => stateConstraint (α t)) _ 0 at H'
  have HE := H.unique H'
  rw [hz] at HE
  convert! HE using 1
  ring

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

private theorem BianchiIX.shearTail_polynomial_variation_bounds {z v : NormalizedState} {L : ℝ}
    (hL : 0 ≤ L) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |curvature (z 2) (z 3) (z 4)| ≤ 2 * shearTailEnergy z ∧
    |shearTailCurvatureDifferential z v| ≤ 4 * shearTailEnergy z * L ∧
    |shearTailCouplingDifferential z v| ≤ 2 * shearTailEnergy z * L := by
  let M := z 2 + z 3 + z 4
  have hM : 0 ≤ M := by dsimp only [M]; positivity [hn.1, hn.2.1, hn.2.2]
  have hM2 : M ^ 2 ≤ 2 * shearTailEnergy z := by
    dsimp only [M, shearTailEnergy]
    nlinarith only [sq_nonneg (z 2), sq_nonneg (z 3 - z 4)]
  have hcoef : |z 2 - z 3 - z 4| ≤ M ∧ |z 3 - z 2 - z 4| ≤ M ∧ |z 4 - z 2 - z 3| ≤ M := by
    dsimp only [M]
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
      linarith only [hn.1, hn.2.1, hn.2.2]
  have HQraw : |shearTailCurvatureDifferential z v| ≤ 2 * M ^ 2 * L := by
    have H := abs_add_three ((z 2 - z 3 - z 4) * v 2) ((z 3 - z 2 - z 4) * v 3)
      ((z 4 - z 2 - z 3) * v 4)
    simp only [abs_mul] at H
    have Hn := mul_le_mul hcoef.1 hv.1 (abs_nonneg _) hM
    have Hx := mul_le_mul hcoef.2.1 hv.2.1 (abs_nonneg _) hM
    have Hy := mul_le_mul hcoef.2.2 hv.2.2 (abs_nonneg _) hM
    dsimp only [shearTailCurvatureDifferential]
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    dsimp only [M] at Hn Hx Hy ⊢
    nlinarith only [H, Hn, Hx, Hy]
  refine ⟨(curvature_abs_le_sum_sq hn.1 hn.2.1 hn.2.2).trans hM2,
    HQraw.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM2 hL]), ?_⟩
  have H := abs_add_three ((z 3 - z 4) * v 2) ((z 2 - 2 * z 3) * v 3) ((2 * z 4 - z 2) * v 4)
  simp only [abs_mul] at H
  have Hn := mul_le_mul (show |z 3 - z 4| ≤ z 3 + z 4 by
    exact abs_le.mpr ⟨by linarith only [hn.2.1], by linarith only [hn.2.2]⟩)
    hv.1 (abs_nonneg _) (add_nonneg hn.2.1 hn.2.2)
  have Hx := mul_le_mul (show |z 2 - 2 * z 3| ≤ z 2 + 2 * z 3 by
    exact abs_le.mpr ⟨by linarith only [hn.1], by linarith only [hn.2.1]⟩)
    hv.2.1 (abs_nonneg _) (by positivity [hn.1, hn.2.1] : 0 ≤ z 2 + 2 * z 3)
  have Hy := mul_le_mul (show |2 * z 4 - z 2| ≤ 2 * z 4 + z 2 by
    exact abs_le.mpr ⟨by linarith only [hn.2.2], by linarith only [hn.1]⟩)
    hv.2.2 (abs_nonneg _) (by positivity [hn.1, hn.2.2] : 0 ≤ 2 * z 4 + z 2)
  dsimp only [shearTailCouplingDifferential, shearTailEnergy]
  nlinarith only [H, Hn, Hx, Hy, mul_nonneg (sq_nonneg (z 2)) hL]

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
open Set

private theorem BianchiIX.shearTail_energy_time_bound {a D t : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hD : 0 ≤ D) (ht : t ∈ Icc (0 : ℝ) (shearTailTime a D))
    (hn : 0 ≤ z 2 ∧ z 2 ≤ a ^ 2 * Real.exp (-2 * t))
    (hx : 0 ≤ z 3 ∧ z 3 ≤ a ^ 2)
    (hy : 0 ≤ z 4 ∧ z 4 ≤ a * Real.exp (-(a / 2) * t)) :
    shearTailEnergy z ≤ 5 * a ^ 2 ∧ t * shearTailEnergy z ≤ (3 + D) * a := by
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have ha3 : a ^ 3 ≤ a ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left ha.2 (sq_nonneg a)]
  have ha4 : a ^ 4 ≤ a ^ 2 := by
    nlinarith only [pow_le_pow_left₀ (sq_nonneg a) ha2 2]
  have hEn : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht.1])
  have hEy : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [ha.1, ht.1])
  have hEyhalf : Real.exp (-(a / 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [ha.1, ht.1])
  have hn2 : z 2 ≤ a ^ 2 := hn.2.trans (mul_le_of_le_one_right (sq_nonneg a) hEn)
  have hy1 : z 4 ≤ a := hy.2.trans (mul_le_of_le_one_right ha.1.le hEyhalf)
  have HF : z 2 ^ 2 + z 2 * (z 3 + z 4) ≤ 3 * a ^ 3 * Real.exp (-2 * t) := by
    have H := mul_le_mul hn.2
      (show z 2 + z 3 + z 4 ≤ 3 * a by linarith only [hn2, hx.2, hy1, ha2])
      (by positivity [hn.1, hx.1, hy.1] : 0 ≤ z 2 + z 3 + z 4)
      (by positivity : 0 ≤ a ^ 2 * Real.exp (-2 * t))
    nlinarith only [H]
  have HX : z 3 ^ 2 ≤ a ^ 4 := by simpa only [← pow_mul] using pow_le_pow_left₀ hx.1 hx.2 2
  have HY : z 4 ^ 2 ≤ a ^ 2 * Real.exp (-a * t) := by
    have H := pow_le_pow_left₀ hy.1 hy.2 2
    have he : (a * Real.exp (-(a / 2) * t)) ^ 2 = a ^ 2 * Real.exp (-a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rwa [he] at H
  have HB : shearTailEnergy z ≤
      3 * a ^ 3 * Real.exp (-2 * t) + a ^ 4 + a ^ 2 * Real.exp (-a * t) := by
    dsimp only [shearTailEnergy]
    linarith only [HF, HX, HY]
  constructor
  · have HF1 := mul_le_of_le_one_right (by positivity [ha.1] : 0 ≤ 3 * a ^ 3) hEn
    have HY1 := mul_le_of_le_one_right (sq_nonneg a) hEy
    nlinarith only [HB, HF1, HY1, ha3, ha4]
  · have Hexp (u : ℝ) : u * Real.exp (-u) ≤ 1 :=
      (Real.mul_exp_neg_le_exp_neg_one u).trans (Real.exp_le_one_iff.mpr (by norm_num))
    have HTF : t * (3 * a ^ 3 * Real.exp (-2 * t)) ≤ (3 / 2 : ℝ) * a ^ 3 := by
      have H := mul_le_mul_of_nonneg_left (Hexp (2 * t)) (by positivity [ha.1] : 0 ≤ 3 * a ^ 3 / 2)
      rw [← neg_mul] at H
      nlinarith only [H]
    have HTY : t * (a ^ 2 * Real.exp (-a * t)) ≤ a := by
      have H := mul_le_mul_of_nonneg_left (Hexp (a * t)) ha.1.le
      rw [← neg_mul] at H
      nlinarith only [H]
    have halog : a * Real.log (1 / a) ≤ 1 := by
      have H := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (one_div_pos.mpr ha.1)) ha.1.le
      have he : a * (1 / a - 1) = 1 - a := by field_simp [ha.1.ne']
      rw [he] at H
      linarith only [H, ha.1]
    have HTX : t * a ^ 4 ≤ D * a := by
      apply (mul_le_mul_of_nonneg_right ht.2 (pow_nonneg ha.1.le 4)).trans
      have he : shearTailTime a D * a ^ 4 = (D * a ^ 2) * (a * Real.log (1 / a)) := by
        dsimp only [shearTailTime]
        field_simp [ha.1.ne']
      rw [he]
      exact (mul_le_of_le_one_right (mul_nonneg hD (sq_nonneg a)) halog).trans
        (mul_le_mul_of_nonneg_left ha2 hD)
    nlinarith only [mul_le_mul_of_nonneg_left HB ht.1, HTF, HTY, HTX, ha3, ha2]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTail_prefix_weighted_energy {a D C q L₀ : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hD : 0 ≤ D) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hL₀ : 0 ≤ L₀ ∧ L₀ ≤ 2 + 4 * C * q * |Real.log a|)
    (hα : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hr : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), shearTailRegion a (α t)) :
    ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D),
      (L₀ + t) * shearTailEnergy (α t) ≤ (13 + 20 * C * q + D) * a := by
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa using ha1)))
  obtain ⟨_, _, _, hN, hX, hY⟩ := hr 0 ⟨le_rfl, hT⟩
  have HW := shearTail_prefix ha hα hc hn hr ⟨hN, hX, hY⟩
  have hlog : a * |Real.log a| ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ha.1) ha.1.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ ha.1.ne'] at H
    rw [abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    nlinarith only [H, ha.1]
  have HL : a * L₀ ≤ 2 + 4 * C * q := by
    have H := mul_le_mul_of_nonneg_left hL₀.2 ha.1.le
    have Hlog := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * C * q)
    nlinarith only [H, Hlog, ha1]
  intro t ht
  have H := HW t ht
  have HB := shearTail_energy_time_bound ⟨ha.1, ha1⟩ hD ht
    ⟨(hn t ht).1, H.1⟩ ⟨(hn t ht).2.1, (hr t ht).2.2.2.2.1⟩
    ⟨(hn t ht).2.2, H.2.2.1.trans
      (mul_le_mul_of_nonneg_right (by linarith only [ha.1] : a / 16 ≤ a) (Real.exp_pos _).le)⟩
  have HBL := mul_le_mul_of_nonneg_left HB.1 hL₀.1
  have HLa := mul_le_mul_of_nonneg_left HL (by positivity [ha.1] : 0 ≤ 5 * a)
  nlinarith only [HB.2, HBL, HLa]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_core_radius_bounds {a : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hc : stateConstraint z = 1)
    (hr : shearTailRegion a z) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : toProjectiveState z 2 < 1) :
    let y := toProjectiveState z
    let k := coreRadius (y 0) (y 2)
    1 < y 0 ∧ 8 ≤ k ∧ 1 / (24 * a) ≤ k ∧ k ≤ 64 / a := by
  intro y k
  obtain ⟨_, _, _, _, _, HAl, HAu⟩ := shearTail_constraint_bounds ha
    (by linarith only [hr.1]) ⟨hr.2.1, hr.2.2.1⟩ ⟨hn.1, hr.2.2.2.1⟩
    ⟨hn.2.1, hr.2.2.2.2.1⟩ ⟨hn.2.2, hr.2.2.2.2.2⟩ hc
  have hA : 0 < 1 + z 0 := (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le HAl
  have hs : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hsqrt : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have HMlo : 1 / (12 * a) ≤ y 0 := by
    change 1 / (12 * a) ≤ Real.sqrt 3 * z 1 / (1 + z 0)
    calc
      _ = (a / 2) / (6 * a ^ 2) := by field_simp [ha.1.ne']; ring
      _ ≤ (Real.sqrt 3 * z 1) / (1 + z 0) := div_le_div₀ (by positivity [ha.1])
        (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt hs.le, hr.2.1]) hA HAu
  have HMhi : y 0 ≤ 60 / a := by
    have H := (shearTail_projectiveCoordinate_le ha.1 HAl ⟨hs.le, hr.2.2.1⟩).2
    convert! H using 1
    field_simp [ha.1.ne']
    ring
  have HM : 1 < y 0 := by
    have H : (2 : ℝ) < 1 / (12 * a) := (lt_div_iff₀ (by positivity [ha.1])).mpr
      (by linarith only [ha.2])
    linarith only [H, HMlo]
  have HKlo : y 0 - 1 ≤ k := phaseNorm_ge (by linarith only [HM])
  have Hscale : 1 / (24 * a) ≤ k := by
    have H : (1 : ℝ) ≤ 1 / (24 * a) := (le_div_iff₀ (by positivity [ha.1])).mpr
      (by linarith only [ha.2])
    have he : 1 / (12 * a) = 2 * (1 / (24 * a)) := by ring
    rw [he] at HMlo
    linarith only [HMlo, HKlo, H]
  have HK8 : 8 ≤ k := (show (8 : ℝ) ≤ 1 / (24 * a) from
    (le_div_iff₀ (by positivity [ha.1])).mpr (by linarith only [ha.2])).trans Hscale
  have HV0 : 0 ≤ y 2 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hn.2.1) hA.le
  have HKhi : k ≤ y 0 := by
    have H := phaseNorm_le_abs_add (y 0 - 1) (y 2)
    rw [abs_of_pos (sub_pos.mpr HM), abs_of_nonneg HV0] at H
    change k ≤ _ at H
    linarith only [H, hv]
  exact ⟨HM, HK8, Hscale, HKhi.trans (HMhi.trans
    (div_le_div_of_nonneg_right (by norm_num) ha.1.le))⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTailProjectiveLogState {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) (hA : 1 + α r 0 ≠ 0) (hs : α r 1 ≠ 0)
    (hn : α r 2 ≠ 0) (hx : α r 3 ≠ 0) (hy : α r 4 ≠ 0) :
    HasDerivAt (fun u => shearTailProjectiveLogState (α u)) (shearTailProjectiveLogVariation (α r) v) r := by
  have Hp := hasDerivAt_pi.mp hα 0
  have H (i : Fin 5) (hi : α r i ≠ 0) :
      HasDerivAt (fun u => Real.log (projectiveCoord (α u 0) (α u i)))
        (v i / α r i - v 0 / (1 + α r 0)) r := by
    have hroot : Real.sqrt (3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    have hcoord : projectiveCoord (α r 0) (α r i) ≠ 0 := div_ne_zero (mul_ne_zero hroot hi) hA
    convert! (hasDerivAt_projectiveCoord Hp (hasDerivAt_pi.mp hα i) hA).log hcoord using 1
    dsimp only [projectiveCoord]
    field_simp
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (Hp.const_add 1).log hA
  · exact H 1 hs
  · exact H 2 hn
  · exact H 3 hx
  · exact H 4 hy

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projective_log_variation_bounds {a K : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hK : 0 ≤ K)
    (hc : stateConstraint z = 1) (hr : shearTailRegion a z) (hn : positiveWalls z)
    (hv : normalizedConstraintDifferential z v = 0)
    (hs : |v 1| ≤ 5) (hL : shearTailEnergy z * shearTailLogSize z v ≤ K * a) :
    let w := shearTailProjectiveLogVariation z v
    |w 0| + |w 1| ≤ (610 + 80 * K) / a ∧
    |w 2| + |w 3| + |w 4| ≤ 3 * shearTailLogSize z v + (900 + 120 * K) / a := by
  intro w
  have Hwall (i : Fin 3) (hi : 0 < z (i.addNat 2)) : |v (i.addNat 2)| ≤ z (i.addNat 2) * shearTailLogSize z v := by
    have H := norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at H
    simpa only [shearTailLogSize, mul_comm] using (div_le_iff₀ hi).mp H
  have HQ := (shearTail_polynomial_variation_bounds (norm_nonneg _) ⟨hn.1.le, hn.2.1.le, hn.2.2.le⟩
    ⟨Hwall 0 hn.1, Hwall 1 hn.2.1, Hwall 2 hn.2.2⟩).2.1
  change |shearTailCurvatureDifferential z v| ≤ 4 * shearTailEnergy z * shearTailLogSize z v at HQ
  have HQ' : |shearTailCurvatureDifferential z v| ≤ 4 * K * a := by nlinarith only [HQ, hL]
  have hp : z 0 < 0 := by linarith only [hr.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  obtain ⟨_, _, _, _, _, HAl, _⟩ := shearTail_constraint_bounds ha hp ⟨hr.2.1, hr.2.2.1⟩
    ⟨hn.1.le, hr.2.2.2.1⟩ ⟨hn.2.1.le, hr.2.2.2.2.1⟩ ⟨hn.2.2.le, hr.2.2.2.2.2⟩ hc
  have hA : 0 < 1 + z 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have Hv0 : |v 0| ≤ (30 + 4 * K) * a := by
    rw [normalizedConstraintDifferential_shearTail] at hv
    have he : (-z 0) * v 0 = z 1 * v 1 + shearTailCurvatureDifferential z v / 2 := by nlinarith only [hv]
    have HE := congrArg abs he
    rw [abs_mul, abs_of_pos (neg_pos.mpr hp)] at HE
    have Habs := abs_add_le (z 1 * v 1) (shearTailCurvatureDifferential z v / 2)
    rw [abs_mul, abs_of_pos hs0, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at Habs
    have Hs := mul_le_mul hr.2.2.1 hs (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 3 * a)
    have Hp := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ -z 0 by linarith only [hr.1]) (abs_nonneg (v 0))
    nlinarith only [HE, Habs, Hs, Hp, HQ']
  have HA : |v 0 / (1 + z 0)| ≤ (300 + 40 * K) / a := by
    rw [abs_div, abs_of_pos hA]
    calc
      _ ≤ ((30 + 4 * K) * a) / (a ^ 2 / 10) := div_le_div₀
        (by positivity [ha.1] : 0 ≤ (30 + 4 * K) * a) Hv0
        (by positivity [ha.1] : 0 < a ^ 2 / 10) HAl
      _ = _ := by field_simp [ha.1.ne']; ring
  have HS : |v 1 / z 1| ≤ 10 / a := by
    rw [abs_div, abs_of_pos hs0]
    calc
      _ ≤ 5 / (a / 2) := div_le_div₀ (by norm_num) hs (by positivity [ha.1]) hr.2.1
      _ = _ := by ring
  have HM := (abs_sub (v 1 / z 1) (v 0 / (1 + z 0))).trans (add_le_add HS HA)
  have HW (i : Fin 3) : |v (i.addNat 2) / z (i.addNat 2) - v 0 / (1 + z 0)| ≤
      shearTailLogSize z v + (300 + 40 * K) / a :=
    (abs_sub _ _).trans (add_le_add (norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i) HA)
  constructor
  · change |v 0 / (1 + z 0)| + |v 1 / z 1 - v 0 / (1 + z 0)| ≤ _
    have H := add_le_add HA HM
    convert! H using 1
    ring
  · have H := add_le_add (add_le_add (HW 0) (HW 1)) (HW 2)
    change |v 2 / z 2 - v 0 / (1 + z 0)| + |v 3 / z 3 - v 0 / (1 + z 0)| +
      |v 4 / z 4 - v 0 / (1 + z 0)| ≤ _ at H
    convert! H using 1
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projective_shear_response {a K r : ℝ} {α : ℝ → NormalizedState} {v : NormalizedState}
    (ha : 0 < a) (hα : HasDerivAt α v r)
    (hA : a ^ 2 / 10 ≤ 1 + α r 0) (hs : 0 < α r 1 ∧ α r 1 ≤ 3 * a)
    (hlog : |shearTailProjectiveLogVariation (α r) v 1| ≤ K / a) :
    HasDerivAt (fun u => projectiveCoord (α u 0) (α u 1))
      (projectiveCoord (α r 0) (α r 1) * shearTailProjectiveLogVariation (α r) v 1) r ∧
    |deriv (fun u => projectiveCoord (α u 0) (α u 1)) r| ≤ 60 * K / a ^ 2 := by
  have hApos : 0 < 1 + α r 0 := (div_pos (sq_pos_of_pos ha) (by norm_num)).trans_le hA
  have HD : HasDerivAt (fun u => projectiveCoord (α u 0) (α u 1))
      (projectiveCoord (α r 0) (α r 1) * shearTailProjectiveLogVariation (α r) v 1) r := by
    convert! hasDerivAt_projectiveCoord (hasDerivAt_pi.mp hα 0) (hasDerivAt_pi.mp hα 1) hApos.ne' using 1
    dsimp [projectiveCoord, shearTailProjectiveLogVariation]
    field_simp [hs.1.ne']
  have HM := shearTail_projectiveCoordinate_le ha hA ⟨hs.1.le, hs.2⟩
  have HM' : projectiveCoord (α r 0) (α r 1) ≤ 60 / a := by
    convert! HM.2 using 1
    field_simp [ha.ne']
    norm_num
  refine ⟨HD, ?_⟩
  rw [HD.deriv, abs_mul, abs_of_nonneg HM.1]
  calc
    _ ≤ (60 / a) * (K / a) := mul_le_mul HM' hlog (abs_nonneg _) (by positivity)
    _ = _ := by ring

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
open Set Filter
open scoped Topology

private theorem BianchiIX.restartShearInitialVariation_tangent {h ζ ν ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ)) :
    HasDerivAt (fun r => restartSectionChart h (restartShearCurve 1 ζ ν r))
      (restartShearInitialVariation h ζ ν ρ) ρ ∧
    normalizedConstraintDifferential (restartSectionChart h (restartShearCurve 1 ζ ν ρ))
      (restartShearInitialVariation h ζ ν ρ) = 0 := by
  have HD := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    ρ (hasDerivAt_restartShearCurve 1 ζ ν ρ)
  refine ⟨HD, ?_⟩
  have HR : Continuous (fun r => restartSectionRadicand h (restartShearCurve 1 ζ ν r)) := by
    unfold restartSectionRadicand restartShearCurve curvature
    fun_prop
  have HE : (fun r => stateConstraint (restartSectionChart h (restartShearCurve 1 ζ ν r))) =ᶠ[𝓝 ρ]
      fun _ => (1 : ℝ) := by
    filter_upwards [HR.continuousAt.eventually (isOpen_Ioi.mem_nhds hrad)] with r hr
    exact restartSectionChart_constraint hr.le
  exact ((hasFDerivAt_stateConstraint _).comp_hasDerivAt ρ HD).unique
    ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq HE)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_projective_control :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let α := fun t => restartShearTailFlow h a q ζ ν t ρ
            let v := fun t => restartShearTailRadialVariation h a q ζ ν t ρ
            let L₀ := shearTailLogSize (α 0) (v 0)
            let K := 13 + 20 * C * q + D
            a ≤ 1 / 256 ∧ 0 ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) T,
              let w := shearTailProjectiveLogVariation (α t) (v t)
              (L₀ + t) * shearTailEnergy (α t) ≤ K * a ∧
              shearTailEnergy (α t) * shearTailLogSize (α t) (v t) ≤ 20 * K * a ∧
              HasDerivAt (fun r => shearTailProjectiveLogState (restartShearTailFlow h a q ζ ν t r)) w ρ ∧
              |w 0| + |w 1| ≤ (1000 + 2400 * K) / a ∧
              |w 2| + |w 3| + |w 4| ≤ (1000 + 2400 * K) * (1 / a + L₀ + t) ∧
              |deriv (fun r => projectiveCoord (restartShearTailFlow h a q ζ ν t r 0)
                (restartShearTailFlow h a q ζ ν t r 1)) ρ| ≤ 60 * (1000 + 2400 * K) / a ^ 2 := by
  obtain ⟨C, hC, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨C, hC, min hR hV, lt_min hhR hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aR, haR, HRa⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aV, haV, HVa⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aR aV, lt_min haR haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T α v L₀ K
  obtain ⟨hasmall, hT, HL₀, _, _, _, _, _, HRt⟩ :=
    HRa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, hrad, _, HT, _⟩ :=
    HVa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have HC : 0 ≤ C := by linarith only [hC]
  have HQ : 0 ≤ q := by linarith only [hq]
  have HK : 0 ≤ K := by dsimp only [K]; positivity
  have HL₀0 : 0 ≤ L₀ := norm_nonneg _
  have Hcon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : stateConstraint (α t) = 1 := (HT t ht).2.2.1
  have Hnon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 := (HT t ht).2.2.2.1
  have Hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : shearTailRegion a (α t) := (HT t ht).2.2.2.2.1
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt α (normalizedField (α t)) t := by
    have H := (hasDerivAt_normalizedMaxCurve (HT t ht).1).scomp t
      ((hasDerivAt_id' t).add_const (q / 2 * Real.log (1 / a)))
    simpa only [Function.comp_def, one_smul, α, restartShearTailFlow] using H
  have HB := shearTail_prefix_weighted_energy ⟨ha.1, hasmall⟩ hD HC HQ ⟨HL₀0, HL₀⟩ HD Hcon Hnon Hreg
  refine ⟨hasmall, hT, ?_⟩
  intro t ht w
  obtain ⟨Hderiv, Hpos, HS, HL, _⟩ := HRt t ht
  have Hb0 : 0 ≤ shearTailEnergy (α t) := by
    dsimp only [shearTailEnergy]
    positivity [(Hnon t ht).1, (Hnon t ht).2.1, (Hnon t ht).2.2]
  have HBL : shearTailEnergy (α t) * shearTailLogSize (α t) (v t) ≤ 20 * K * a := by
    have H := mul_le_mul_of_nonneg_left HL Hb0
    have Hextra := mul_nonneg Hb0 HL₀0
    nlinarith only [H, HB t ht, Hextra]
  have Hv : normalizedConstraintDifferential (α t) (v t) = 0 := by
    have H := congrArg (fun L : NormalizedState →L[ℝ] ℝ => L (restartShearInitialVariation h ζ ν ρ))
      (normalizedConstraintDifferential_flow (HT t ht).1)
    simp only [ContinuousLinearMap.comp_apply] at H
    exact H.trans (restartShearInitialVariation_tangent hrad).2
  have HP := shearTail_projective_log_variation_bounds ⟨ha.1, hasmall⟩
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) HK) (Hcon t ht) (Hreg t ht) Hpos Hv HS HBL
  have HAl : a ^ 2 / 10 ≤ 1 + α t 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, HAl, _, _⟩ := HT t ht
    exact HAl
  have hA : 0 < 1 + α t 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have hs : 0 < α t 1 := by linarith only [(Hreg t ht).2.1, ha.1]
  have Hsum : |w 0| + |w 1| ≤ (1000 + 2400 * K) / a :=
    HP.1.trans ((div_le_div_iff_of_pos_right ha.1).mpr (by nlinarith only [HK]))
  refine ⟨HB t ht, HBL, hasDerivAt_shearTailProjectiveLogState Hderiv hA.ne' hs.ne'
    Hpos.1.ne' Hpos.2.1.ne' Hpos.2.2.ne', Hsum, ?_, ?_⟩
  · have Hfrac : (900 + 120 * (20 * K)) / a ≤ (1000 + 2400 * K) * (1 / a) := by
      rw [mul_one_div]
      exact (div_le_div_iff_of_pos_right ha.1).mpr (by linarith)
    calc
      _ ≤ 3 * shearTailLogSize (α t) (v t) + (900 + 120 * (20 * K)) / a := HP.2
      _ ≤ 6 * L₀ + 60 * t + (1000 + 2400 * K) * (1 / a) :=
        add_le_add (by linarith only [HL]) Hfrac
      _ ≤ _ := by nlinarith only [mul_nonneg HK HL₀0, mul_nonneg HK ht.1, HL₀0, ht.1]
  · exact (shearTail_projective_shear_response ha.1 Hderiv HAl ⟨hs, (Hreg t ht).2.2.1⟩
      (show |w 1| ≤ (1000 + 2400 * K) / a by linarith only [Hsum, abs_nonneg (w 0)])).2

end
end

/-- The exact tail supplies all entrance data, with the logarithmic loss retained only in wall responses. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ B > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∀ δ ∈ Ioc (0 : ℝ) (1 / 10000),
          ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
            let k := coreRadius (Y ρ 0) (Y ρ 2)
            let L := 1 + |Real.log a|
            DifferentiableAt ℝ Y ρ ∧ 8 ≤ k ∧ 1 / (24 * a) ≤ k ∧ k ≤ 64 / a ∧
            1 < Y ρ 0 ∧ (0 < Y ρ 1 ∧ Y ρ 1 ≤ δ) ∧ (0 < Y ρ 2 ∧ Y ρ 2 < 1) ∧
            (0 < Y ρ 3 ∧ Y ρ 3 ≤ δ) ∧ L * (Y ρ 1 + Y ρ 3) ≤ 1 ∧
            |deriv (fun r => Y r 0) ρ| ≤ B * k ^ 2 ∧
            ∀ i : Fin 4, i ≠ 0 → |deriv (fun r => Y r i) ρ| ≤ B * L * k * Y ρ i := by
  obtain ⟨CR, hCR, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨CP, hCP, hP, hhP, HP⟩ := exists_restartShearTail_projective_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hR (min hP hV), lt_min hhR (lt_min hhP hhV), ?_⟩
  intro h hh q D hq hD
  have hCR0 : 0 ≤ CR := by linarith only [hCR]
  have hCP0 : 0 ≤ CP := by linarith only [hCP]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hD0 : 0 ≤ D := by linarith only [hD]
  let M := 1000 + 2400 * (13 + 20 * CP * q + D)
  let N := 3 + 4 * CR * q + D
  let B := 60000 * M * N
  have hM : 0 < M := by dsimp only [M]; positivity
  have hN : 1 ≤ N := by dsimp only [N]; nlinarith only [mul_nonneg hCR0 hq0, hD0]
  have hN0 : 0 < N := by linarith only [hN]
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro P hPexp δ hδ
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD0 hPexp
  obtain ⟨aP, haP, HAP⟩ := HP h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D P hq hD0 hPexp
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ q D P hq hD0 hPexp
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_entrance_wall_scale (h := h) hq hD hδ.1
  refine ⟨min aR (min aP (min aV aS)), lt_min haR (lt_min haP (lt_min haV haS)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y k L
  let T := shearTailTime a D
  let z := restartShearTailFlow h a q ζ ν T ρ
  let v := restartShearTailRadialVariation h a q ζ ν T ρ
  let L₀ := shearTailLogSize (restartShearTailFlow h a q ζ ν 0 ρ)
    (restartShearTailRadialVariation h a q ζ ν 0 ρ)
  let w := shearTailProjectiveLogVariation z v
  obtain ⟨hasmall, hT, HL₀, _, _, _, _, _, HRT⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, HPT⟩ := HAP a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, HVT, Hpowers⟩ :=
    HAV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
      ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  obtain ⟨ha1, Hsmall⟩ := HAS a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨HD, Hpos, _, _, _⟩ := HRT T ⟨hT, le_rfl⟩
  obtain ⟨_, _, HDlog, _, HWlog, HMder⟩ := HPT T ⟨hT, le_rfl⟩
  obtain ⟨_, _, Hcon, Hnon, Hreg, _, _, _, _, HAl, _, HVlt⟩ := HVT T ⟨hT, le_rfl⟩
  have hA : 0 < 1 + z 0 := (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le HAl
  have HY : DifferentiableAt ℝ Y ρ :=
    ((contDiffAt_toProjectiveState 1 hA.ne').differentiableAt (by norm_num)).comp ρ HD.differentiableAt
  obtain ⟨hm, hk8, hklo, hkhi⟩ := shearTail_core_radius_bounds ⟨ha.1, hasmall⟩ Hcon Hreg Hnon HVlt
  change 8 ≤ k at hk8
  change 1 / (24 * a) ≤ k at hklo
  change k ≤ 64 / a at hkhi
  have HPpos := toProjectiveState_positive hA Hpos
  change 0 < Y ρ 1 ∧ 0 < Y ρ 2 ∧ 0 < Y ρ 3 at HPpos
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [abs_nonneg (Real.log a)]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have Hwall : Y ρ 1 + Y ρ 3 ≤ 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) := by
    have hε1 : ε ≤ 1 := by linarith only [hε.2]
    have Hε := mul_le_mul_of_nonneg_right hε1 (by positivity [ha.1] : 0 ≤ 80 * a ^ (D / 2 - 1))
    have Hn : Y ρ 1 ≤ 20 * h * a ^ (q - 2) := Hpowers.1
    have Hy : Y ρ 3 ≤ 80 * ε * a ^ (D / 2 - 1) := Hpowers.2.2
    nlinarith only [Hn, Hy, Hε]
  have HLwall : L * (Y ρ 1 + Y ρ 3) ≤ δ := by
    have H := mul_le_mul_of_nonneg_right Hwall hL0
    change (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) * L ≤ δ at Hsmall
    nlinarith only [H, Hsmall]
  have Hsum : Y ρ 1 + Y ρ 3 ≤ δ := by
    have H := mul_le_mul_of_nonneg_right hL (add_nonneg HPpos.1.le HPpos.2.2.le)
    linarith only [H, HLwall]
  have htime : a * T = D * |Real.log a| := by
    dsimp only [T, shearTailTime]
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) ha.1.ne', Real.log_one, zero_sub,
      abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    field_simp [ha.1.ne']
  have Hbudget : 1 / a + L₀ + T ≤ N * L / a := by
    apply (le_div_iff₀ ha.1).mpr
    have H := mul_le_mul_of_nonneg_left HL₀ ha.1.le
    have HC := mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ 4 * CR * q * |Real.log a|)
    have HI : (1 / a) * a = 1 := by field_simp [ha.1.ne']
    dsimp only [N, L]
    nlinarith only [H, HC, HI, htime, ha1, mul_nonneg hCR0 hq0, hD0, abs_nonneg (Real.log a)]
  have HW : |w 2| + |w 3| + |w 4| ≤ M * N * L / a := HWlog.trans
    ((mul_le_mul_of_nonneg_left Hbudget hM.le).trans_eq (by ring))
  have hki : 1 / a ≤ 24 * k := by
    calc
      _ = 24 * (1 / (24 * a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hklo (by norm_num)
  have hBshear : 34560 * M ≤ B := by
    dsimp only [B]
    nlinarith only [mul_le_mul_of_nonneg_left hN hM.le, hM]
  have Hdm : |deriv (fun r => Y r 0) ρ| ≤ B * k ^ 2 := HMder.trans (by
    calc
      _ = 60 * M * (1 / a) ^ 2 := by ring
      _ ≤ 60 * M * (24 * k) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity [ha.1]) hki 2) (by positivity)
      _ = 34560 * M * k ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBshear (sq_nonneg k))
  have Hlog (i : Fin 4) : HasDerivAt (fun r => Real.log (Y r i)) (w i.succ) ρ := by
    fin_cases i
    · exact hasDerivAt_pi.mp HDlog 1
    · exact hasDerivAt_pi.mp HDlog 2
    · exact hasDerivAt_pi.mp HDlog 3
    · exact hasDerivAt_pi.mp HDlog 4
  have HwallDer (i : Fin 4) (hi : i ≠ 0) :
      |deriv (fun r => Y r i) ρ| ≤ B * L * k * Y ρ i := by
    have hy : 0 < Y ρ i := by
      fin_cases i
      · exact (hi rfl).elim
      · exact HPpos.1
      · exact HPpos.2.1
      · exact HPpos.2.2
    have hw : |w i.succ| ≤ M * N * L / a := by
      fin_cases i
      · exact (hi rfl).elim
      · change |w 2| ≤ _
        linarith only [HW, abs_nonneg (w 3), abs_nonneg (w 4)]
      · change |w 3| ≤ _
        linarith only [HW, abs_nonneg (w 2), abs_nonneg (w 4)]
      · change |w 4| ≤ _
        linarith only [HW, abs_nonneg (w 2), abs_nonneg (w 3)]
    have Hlog' := ((differentiableAt_pi.mp HY i).hasDerivAt).log hy.ne'
    have Heq := Hlog'.unique (Hlog i)
    have Habs : |deriv (fun r => Y r i) ρ| ≤ Y ρ i * (M * N * L / a) := by
      rw [← Heq, abs_div, abs_of_pos hy] at hw
      simpa only [mul_comm] using (div_le_iff₀ hy).mp hw
    have HBwall : 24 * M * N ≤ B := by dsimp only [B]; nlinarith only [mul_pos hM hN0]
    calc
      _ ≤ Y ρ i * (M * N * L / a) := Habs
      _ ≤ Y ρ i * (M * N * L * (24 * k)) := by
        rw [div_eq_mul_inv, show a⁻¹ = 1 / a by ring]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hki (by positivity)) hy.le
      _ = (24 * M * N) * L * k * Y ρ i := by ring
      _ ≤ _ := by
        have hk0 : 0 ≤ k := by linarith only [hk8]
        nlinarith only [mul_le_mul_of_nonneg_right HBwall (by positivity : 0 ≤ L * k * Y ρ i)]
  exact ⟨HY, hk8, hklo, hkhi, hm,
    ⟨HPpos.1, by linarith only [Hsum, HPpos.2.2]⟩, ⟨HPpos.2.1, HVlt⟩,
    ⟨HPpos.2.2, by linarith only [Hsum, HPpos.1]⟩,
    HLwall.trans (hδ.2.trans (by norm_num)), Hdm, HwallDer⟩
