-- Prove2me | solution 1 for BianchiIX.exists_stableStrongProjectionError_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:23:13.790953+00:00
-- url     : https://prove2.me/submissions/a2aadfe7-d891-4ed8-ae8c-aac3dc8f20a0

import Definitions.Def_BianchiIX_Analysis_CoordinateFactor
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_exists_stableBoundaryProjection_refined_derivatives
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_fderiv_apply_const {f : E → F} {gamma : ℝ → E} {v : E} {t : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (gamma t))
    (hg : HasDerivAt gamma v t) (w : E) :
    HasDerivAt (fun s => fderiv ℝ f (gamma s) w)
      (fderiv ℝ (fderiv ℝ f) (gamma t) v w) t := by
  have H := (hf.hasFDerivAt.comp_hasDerivAt t hg).clm_apply (hasDerivAt_const t w)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasDerivAt_coordinateSegment {n : ℕ} (i : Fin n) (Y : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (coordinateSegment i Y) (Y i • Pi.single i 1) s := by
  convert! (hasDerivAt_update Y i (s * Y i)).scomp s ((hasDerivAt_id s).mul_const (Y i)) using 1
  simp only [one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coordinate_difference_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {i : Fin n} {Y : Fin n → ℝ} {C : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (coordinateSegment i Y s))
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, |fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)| ≤ C) :
    |f Y - f (Function.update Y i 0)| ≤ |Y i| * C := by
  have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => f (coordinateSegment i Y t))
        (Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)) s := by
    convert! (hf s hs).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_coordinateSegment i Y s) using 1
    simp only [map_smul, smul_eq_mul]
  have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)‖ ≤ |Y i| * C := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC s hs) (abs_nonneg _)
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (HD s hs).hasDerivWithinAt) HB (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa [coordinateSegment] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coordinate_fderiv_difference_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {i : Fin n} {Y v : Fin n → ℝ} {C : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fderiv ℝ f) (coordinateSegment i Y s))
    (hC : ∀ s ∈ Icc (0 : ℝ) 1,
      |fderiv ℝ (fderiv ℝ f) (coordinateSegment i Y s) (Pi.single i 1) v| ≤ C) :
    |fderiv ℝ f Y v - fderiv ℝ f (Function.update Y i 0) v| ≤ |Y i| * C := by
  have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => fderiv ℝ f (coordinateSegment i Y t) v)
        (Y i * fderiv ℝ (fderiv ℝ f) (coordinateSegment i Y s) (Pi.single i 1) v) s := by
    convert! hasDerivAt_fderiv_apply_const (hf s hs) (hasDerivAt_coordinateSegment i Y s) v using 1
    simp only [map_smul, smul_apply, smul_eq_mul]
  have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖Y i * fderiv ℝ (fderiv ℝ f) (coordinateSegment i Y s) (Pi.single i 1) v‖ ≤ |Y i| * C := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC s hs) (abs_nonneg _)
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (HD s hs).hasDerivWithinAt) HB (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa [coordinateSegment] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryProjection_two {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y :=
  contDiffAt_stableBoundaryProjection_two_in_band hm (by simp) hu hw

end
end

private theorem BianchiIX.stableStrongBase_apply (y : StableState) : stableStrongBase y = ![y 0, y 1, 0] := by
  ext i; fin_cases i <;> rfl

private theorem BianchiIX.stableStrongBase_eq_update (y : StableState) : stableStrongBase y = Function.update y 2 0 := by
  ext i; fin_cases i <;> simp [stableStrongBase_apply]

private theorem BianchiIX.stableStrongProjectionError_differential {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 stableStrongProjectionError y ∧
      ∀ d : StableState,
      fderiv ℝ stableStrongProjectionError y d =
        fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y d -
        fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
          (stableStrongBase y) (stableStrongBase d) := by
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have HP : ContDiffAt ℝ 2 P y := contDiffAt_stableBoundaryProjection_two hm hu hw
  have HQ : ContDiffAt ℝ 2 P (stableStrongBase y) :=
    contDiffAt_stableBoundaryProjection_two hm hu (by change |(0 : ℝ)| < 1 / 200; norm_num)
  have HR := HP.sub (HQ.comp y stableStrongBase.contDiff.contDiffAt)
  have HD := (HP.differentiableAt (by norm_num)).hasFDerivAt.sub
    ((HQ.differentiableAt (by norm_num)).hasFDerivAt.comp y stableStrongBase.hasFDerivAt)
  change ContDiffAt ℝ 2 stableStrongProjectionError y at HR
  change HasFDerivAt stableStrongProjectionError _ y at HD
  refine ⟨HR, ?_⟩
  intro d
  rw [HD.fderiv]
  rfl


/-- Both the value and the two tangential derivatives retain the removed weak wall. -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      let L := y 0 + 1
      |stableStrongProjectionError y| ≤ C * |y 2| * b / L ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 0 1)| ≤ C * |y 2| * b / L ^ 2 ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 1 1)| ≤ C * |y 2| / L ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 2 1)| ≤ C * b / L := by
  obtain ⟨C, hC, HC⟩ := exists_stableBoundaryProjection_refined_derivatives
  refine ⟨C, hC, ?_⟩
  intro y hm hu hw b L
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have hL : 0 < L := by dsimp only [L]; linarith only [hm]
  have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |coordinateSegment 2 y s 1| < 1 / 200 ∧ |coordinateSegment 2 y s 2| < 1 / 200 ∧
      |coordinateSegment 2 y s 1| + |coordinateSegment 2 y s 2| ≤ b := by
    have H : |s * y 2| ≤ |y 2| := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hs.2
    simpa [coordinateSegment, b] using And.intro hu (And.intro (H.trans_lt hw) (add_le_add_left H |y 1|))
  have Hreg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 2 P (coordinateSegment 2 y s) :=
    contDiffAt_stableBoundaryProjection_two (by simpa [coordinateSegment] using hm) (hseg s hs).1 (hseg s hs).2.1
  have Hwall (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |fderiv ℝ P (coordinateSegment 2 y s) (Pi.single 2 1)| ≤ C / L * b := by
    have H := (HC (coordinateSegment 2 y s) (by simpa [coordinateSegment] using hm)
      (hseg s hs).1 (hseg s hs).2.1).2.1 (Pi.single 2 1) (by simp)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    change _ ≤ C / L * _ at H
    exact H.trans (mul_le_mul_of_nonneg_left (hseg s hs).2.2 (by positivity))
  have Hmixed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |fderiv ℝ (fderiv ℝ P) (coordinateSegment 2 y s) (Pi.single 2 1) (Pi.single 0 1)| ≤ C / L ^ 2 * b := by
    rw [((Hreg s hs).isSymmSndFDerivAt (by norm_num)).eq (Pi.single 2 1) (Pi.single 0 1)]
    have H := (HC (coordinateSegment 2 y s) (by simpa [coordinateSegment] using hm)
      (hseg s hs).1 (hseg s hs).2.1).2.2.2.1 (Pi.single 0 1) (Pi.single 2 1) (by simp) (by simp) (by simp)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    change _ ≤ C / L ^ 2 * _ at H
    exact H.trans (mul_le_mul_of_nonneg_left (hseg s hs).2.2 (by positivity))
  have Hstable (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |fderiv ℝ (fderiv ℝ P) (coordinateSegment 2 y s) (Pi.single 2 1) (Pi.single 1 1)| ≤ C / L := by
    have H := (HC (coordinateSegment 2 y s) (by simpa [coordinateSegment] using hm)
      (hseg s hs).1 (hseg s hs).2.1).2.2.2.2 (Pi.single 2 1) (Pi.single 1 1) (by simp) (by simp)
    simpa [Pi.norm_single, coordinateSegment, L] using H
  have Hval := coordinate_difference_bound (fun s hs => (Hreg s hs).differentiableAt (by norm_num)) Hwall
  have Hrad := coordinate_fderiv_difference_bound
    (fun s hs => ((Hreg s hs).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)) Hmixed
  have Hstrong := coordinate_fderiv_difference_bound
    (fun s hs => ((Hreg s hs).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)) Hstable
  have HD := (stableStrongProjectionError_differential hm hu hw).2
  have Hb0 : stableStrongBase (Pi.single 0 1) = Pi.single 0 1 := by ext i; fin_cases i <;> simp [stableStrongBase_apply]
  have Hb1 : stableStrongBase (Pi.single 1 1) = Pi.single 1 1 := by ext i; fin_cases i <;> simp [stableStrongBase_apply]
  have Hb2 : stableStrongBase (Pi.single 2 1) = 0 := by ext i; fin_cases i <;> simp [stableStrongBase_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change |stableStrongProjectionError y| ≤ _ at Hval
    convert Hval using 1; ring
  · rw [HD, Hb0, stableStrongBase_eq_update]
    convert Hrad using 1; ring
  · rw [HD, Hb1, stableStrongBase_eq_update]
    convert Hstrong using 1; ring
  · rw [HD, Hb2, map_zero, sub_zero]
    have H := Hwall 1 (by norm_num)
    simp only [coordinateSegment, one_mul, Function.update_eq_self] at H
    convert H using 1; ring
