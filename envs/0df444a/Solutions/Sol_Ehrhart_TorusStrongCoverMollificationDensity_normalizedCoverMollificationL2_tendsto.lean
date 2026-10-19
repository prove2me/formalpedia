-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollificationL2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/71532575-7164-418c-96ba-8c6a70beda52

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongCoverMollification_normalizedCoverMollification_continuous_compact_L2_tendsto
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollificationL2_dist_le
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollificationL2_toLp

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongCoverMollificationDensity
theorem _root_.solution
    {n : ℕ}
    (u : MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n))) :
    Tendsto
      (fun k : ℕ => normalizedCoverMollificationL2 k u)
      atTop (nhds u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  have hdense :
      Dense
        {v : MeasureTheory.Lp ℂ 2
            (volume : Measure (LogSpace n)) |
          ∃ g : LogSpace n → ℂ,
            v =ᵐ[(volume : Measure (LogSpace n))] g ∧
              HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  obtain ⟨v, ⟨g, hvg, hgs, hgd⟩, huv⟩ :=
    hdense.exists_dist_lt u hquarter
  let hg : MemLp g 2 (volume : Measure (LogSpace n)) :=
    hgd.continuous.memLp_of_hasCompactSupport hgs
  have hv : v = hg.toLp g := by
    apply MeasureTheory.Lp.ext
    exact hvg.trans hg.coeFn_toLp.symm
  have hvconv :
      Tendsto
        (fun k : ℕ => normalizedCoverMollificationL2 k v)
        atTop (nhds v) := by
    subst v
    simpa only [normalizedCoverMollificationL2_toLp] using
      normalizedCoverMollification_continuous_compact_L2_tendsto
        hgd.continuous hgs
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp hvconv) (ε / 4) hquarter
  refine ⟨N, fun k hk => ?_⟩
  calc
    dist (normalizedCoverMollificationL2 k u) u ≤
        dist (normalizedCoverMollificationL2 k u)
          (normalizedCoverMollificationL2 k v) +
        dist (normalizedCoverMollificationL2 k v) v +
        dist v u := by
          calc
            dist (normalizedCoverMollificationL2 k u) u ≤
                dist (normalizedCoverMollificationL2 k u)
                  (normalizedCoverMollificationL2 k v) +
                dist (normalizedCoverMollificationL2 k v) u :=
                  dist_triangle _ _ _
            _ ≤ _ := by
              linarith [dist_triangle
                (normalizedCoverMollificationL2 k v) v u]
    _ ≤ dist u v +
        dist (normalizedCoverMollificationL2 k v) v +
        dist v u := by
          gcongr
          exact normalizedCoverMollificationL2_dist_le k u v
    _ < ε := by
          rw [dist_comm v u]
          nlinarith [hN k hk]
end Ehrhart.TorusStrongCoverMollificationDensity
