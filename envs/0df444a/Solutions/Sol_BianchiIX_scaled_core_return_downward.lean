-- Prove2me | solution 1 for BianchiIX.scaled_core_return_downward
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:05:01.357763+00:00
-- url     : https://prove2.me/submissions/a408af74-7ea7-440b-a216-7ca581cc61fe

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

private theorem BianchiIX.deriv_nonpos_of_left_lower {f : ℝ → ℝ} {a b d : ℝ} (hab : a < b)
    (hf : HasDerivAt f d b) (hlower : ∀ t ∈ Ioo a b, f b ≤ f t) : d ≤ 0 := by
  apply le_of_tendsto (hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE b))
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hlower t ht)) (sub_nonpos.mpr ht.2.le)

end
end

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
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_lt_right_of_deriv_neg {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hd : d < 0) : ∀ᶠ t in 𝓝[>] a, f t < f a := by
  have H := eventually_gt_right_of_deriv_pos hf.neg (neg_pos.mpr hd)
  exact H.mono fun _ h => neg_lt_neg_iff.mp h

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

/-- Any later return approached from above is on the outgoing branch and is transverse. -/
theorem solution {β : ℝ → ProjectiveState} {s t a k : ℝ}
    (hk : 6 ≤ k) (hst : s < t) (ha : 0 < a)
    (hβ : HasDerivAt β (a • projectiveField (β t)) t)
    (hv : β t 2 = 1) (habove : ∀ u ∈ Ioo s t, 1 ≤ β u 2)
    (hr : 99 / 100 * k ≤ coreRadius (β t 0) (β t 2))
    (hu : 0 ≤ β t 1 ∧ β t 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ β t 3 ∧ β t 3 ≤ (1 / 10000) / k) :
    β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -a * k / 2 ∧
      ∀ᶠ u in 𝓝[>] t, β u 2 < 1 := by
  have hd : HasDerivAt (fun u => β u 2) (a * activeVelocity (β t 0) (β t 1) 1 (β t 3)) t := by
    have H := hasDerivAt_pi.mp hβ 2
    change HasDerivAt (fun u => β u 2) (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) t at H
    rwa [hv] at H
  have hnonpos := deriv_nonpos_of_left_lower hst hd (fun u hh => by rw [hv]; exact habove u hh)
  rw [hv] at hr
  obtain h | h := core_section_velocity hk hr hu hw
  · have H : 0 < a * activeVelocity (β t 0) (β t 1) 1 (β t 3) :=
      mul_pos ha (lt_of_lt_of_le (by linarith : 0 < k / 2) h.2)
    linarith
  · have hvel := mul_le_mul_of_nonneg_left h.2 ha.le
    have hneg : a * activeVelocity (β t 0) (β t 1) 1 (β t 3) < 0 := by
      have H : a * (-k / 2) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
      exact hvel.trans_lt H
    refine ⟨h.1, ?_, ?_, ?_⟩
    · rw [hv]
      exact (coreAngle_section_sign _).2.mpr h.1
    · rw [hd.deriv]
      nlinarith
    · simpa only [hv] using eventually_lt_right_of_deriv_neg hd hneg
