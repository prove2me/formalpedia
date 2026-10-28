-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_origin_value_of_vanishing_residual
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:47:35.295207+00:00
-- url     : https://prove2.me/submissions/0f6d6aab-50eb-4a2d-9c6a-cc6b4d37989f

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.Field.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
theorem solution
    (a : ℝ) (g C : ℝ → ℝ) (ha : 0 < a)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hC : Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 0))
    (heq : ∀ x : ℝ, 0 < x → a * g x + C x = 1) :
    g 0 = 1 / a := by
  have h1 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
    ((hg 0 (le_refl (0:ℝ))).mono Ioi_subset_Ici_self).tendsto
  have h2 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 ((1 - 0) / a)) := by
    refine ((tendsto_const_nhds.sub hC).div_const a).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have := heq x hx
    field_simp
    linarith
  rw [tendsto_nhds_unique h1 h2]
  ring
