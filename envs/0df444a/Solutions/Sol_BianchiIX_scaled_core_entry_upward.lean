-- Prove2me | solution 1 for BianchiIX.scaled_core_entry_upward
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:05:28.023049+00:00
-- url     : https://prove2.me/submissions/dd374520-bb29-4b1c-a3b9-69f72d72962d

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_core_section_velocity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_gt_right_of_deriv_pos {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hd : 0 < d) : ∀ᶠ t in 𝓝[>] a, f a < f t := by
  have H := (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)).eventually
    (isOpen_Ioi.mem_nhds hd)
  filter_upwards [H, self_mem_nhdsWithin] with t ht hat
  rw [slope_def_field] at ht
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hat)).mp ht)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_section_sign (m : ℝ) :
    (coreAngle m 1 < 0 ↔ 1 < m) ∧ (0 < coreAngle m 1 ↔ m < 1) := by
  simp only [coreAngle, div_one, Real.arsinh_neg_iff, Real.arsinh_pos_iff]
  constructor <;> constructor <;> intro h <;> linarith

end
end

theorem solution {β : ℝ → ProjectiveState} {s a k : ℝ}
    (hk : 6 ≤ k) (ha : 0 < a)
    (hβ : HasDerivAt β (a • projectiveField (β s)) s)
    (hv : β s 2 = 1) (hm : 1 ≤ β s 0)
    (hr : 99 / 100 * k ≤ coreRadius (β s 0) (β s 2))
    (hu : 0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ β s 3 ∧ β s 3 ≤ (1 / 10000) / k) :
    coreAngle (β s 0) (β s 2) < 0 ∧
      a * k / 2 ≤ deriv (fun u => β u 2) s ∧ ∀ᶠ u in 𝓝[>] s, 1 < β u 2 := by
  have hd := hasDerivAt_pi.mp hβ 2
  change HasDerivAt (fun u => β u 2) (a * activeVelocity (β s 0) (β s 1) (β s 2) (β s 3)) s at hd
  rw [hv] at hd hr
  obtain h | h := core_section_velocity hk hr hu hw
  · have hvel := mul_le_mul_of_nonneg_left h.2 ha.le
    have hpos : 0 < a * activeVelocity (β s 0) (β s 1) 1 (β s 3) :=
      mul_pos ha (lt_of_lt_of_le (by linarith : 0 < k / 2) h.2)
    refine ⟨?_, ?_, ?_⟩
    · rw [hv]
      exact (coreAngle_section_sign _).1.mpr h.1
    · rw [hd.deriv]
      nlinarith
    · simpa only [hv] using eventually_gt_right_of_deriv_pos hd hpos
  · linarith [h.1]
