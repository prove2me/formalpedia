-- Prove2me | solution 1 for Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction.sourceRadialCutoff_eventually_one_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/609769e0-f111-4e02-8096-b135648eaac8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedResolventConstantCore MatrixTorusBochnerCoreDensity
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction
theorem _root_.solution
    {n : ℕ} {s : Set (LogTorus n)}
    (hs : IsCompact s) :
    ∀ᶠ m : ℕ in atTop,
      ∀ q ∈ s, sourceRadialCutoff m q = 1 := by
  have hrad : IsCompact
      ((fun q : LogTorus n => q.1) '' s) :=
    hs.image continuous_fst
  obtain ⟨R, hR⟩ := hrad.exists_bound_of_continuousOn
    (continuous_id : Continuous
      (fun x : Space n => x)).continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with m hm
  intro q hq
  change growingBump m q.1 = 1
  apply (growingBump m).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖q.1‖ ≤ (m : ℝ) + 1
  have hNm : (N : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hqR := hR q.1 ⟨q, hq, rfl⟩
  change ‖q.1‖ ≤ R at hqR
  linarith
end Ehrhart.RadialPhysicalResolventRootCutoffUniformExtraction
