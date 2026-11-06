-- Prove2me | solution 1 for BianchiIX.exists_common_rpow_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:05:22.874845+00:00
-- url     : https://prove2.me/submissions/07a00105-9e40-4a6b-8cc7-648b5c40d45c

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- Finitely many positive-power errors admit one common amplitude threshold. -/
theorem solution {ι : Type*} (s : Finset ι) {C p ε : ι → ℝ} {upper : ℝ}
    (hC : ∀ i ∈ s, 0 ≤ C i) (hp : ∀ i ∈ s, 0 < p i)
    (hε : ∀ i ∈ s, 0 < ε i) (hu : 0 < upper) :
    ∃ Bmax : ℝ, 0 < Bmax ∧ Bmax < upper ∧
      ∀ B ∈ Ioc 0 Bmax, ∀ i ∈ s, C i * B ^ p i < ε i := by
  have he : ∀ᶠ B : ℝ in 𝓝 0, ∀ i ∈ s, C i * B ^ p i < ε i := by
    apply (s.eventually_all).mpr
    intro i hi
    have H : Tendsto (fun B : ℝ => C i * B ^ p i) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (ne_of_gt (hp i hi)), mul_zero] using
        ((Real.continuousAt_rpow_const 0 (p i) (Or.inr (hp i hi).le)).tendsto.const_mul (C i))
    exact H.eventually (gt_mem_nhds (hε i hi))
  have hpos : ∀ᶠ B : ℝ in 𝓝[>] 0, 0 < B := self_mem_nhdsWithin
  have hupper : ∀ᶠ B : ℝ in 𝓝[>] 0, B < upper :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hu)
  have hsmall := he.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  obtain ⟨Bmax, hpos, hupper, hbudget⟩ := (hpos.and (hupper.and hsmall)).exists
  refine ⟨Bmax, hpos, hupper, fun B hB i hi => ?_⟩
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hB.1.le hB.2 (hp i hi).le)
    (hC i hi)).trans_lt (hbudget i hi)
