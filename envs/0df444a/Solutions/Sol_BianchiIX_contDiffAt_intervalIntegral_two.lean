-- Prove2me | solution 1 for BianchiIX.contDiffAt_intervalIntegral_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:10:01.079032+00:00
-- url     : https://prove2.me/submissions/2f1f0c04-1fe9-41aa-83b0-714254b8557f

import Theorems.Thm_BianchiIX_contDiffAt_compact_vector_integral
import Theorems.Thm_BianchiIX_hasFDerivAt_intervalIntegral_of_contDiffAt
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution {F : E × ℝ → ℝ} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 2 F (x, t)) :
    ContDiffAt ℝ 2 (fun y => ∫ t in a..b, F (y, t)) x := by
  let D : E × ℝ → E →L[ℝ] ℝ := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD (t : ℝ) (ht : t ∈ Icc a b) : ContDiffAt ℝ 1 D (x, t) :=
    ((hF t ht).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_comp contDiffAt_const
  have hs : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (y, t) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    exact ((hF t ht).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).eventually (by norm_num)
  change ContDiffAt ℝ ((1 : ℕ) + 1) (fun y => ∫ t in a..b, F (y, t)) x
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ t in a..b, D (y, t), ⟨_, hs, ?_⟩,
    contDiffAt_compact_vector_integral hab hD⟩
  intro y hy
  exact hasFDerivAt_intervalIntegral_of_contDiffAt hab hy
