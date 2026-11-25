-- Prove2me | solution 1 for FiniteEnergyPlane.continuousAt_reeb
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T13:09:14.290998+00:00
-- url     : https://prove2.me/submissions/70702c74-4a00-4c90-a2a0-3724faf925e3

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_reeb_spec



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem continuousAt_reeb_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContinuousAt (reeb H) x := by
  have hg : Continuous (grad H) := by
    refine continuous_pi fun k => ?_
    exact ((hH.1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hj : Continuous (fun x : V n => j0 x) := by
    refine continuous_pi fun k => ?_
    unfold j0
    by_cases hk : (k : ℕ) % 2 = 0
    · simp only [hk, dif_pos]; fun_prop
    · simp only [hk, dif_neg, not_false_iff]; fun_prop
  have hh : Continuous (hamVF H) := hj.comp hg
  have hl : Continuous (fun x : V n => liouville x (hamVF H x)) := by
    unfold liouville omega0 dot
    refine (continuous_finsetSum _ fun k _ => ?_).div_const _
    exact ((continuous_apply k).comp hj).mul ((continuous_apply k).comp hh)
  refine (hl.continuousAt.inv₀ ?_).smul hh.continuousAt
  exact (reeb_spec H hH _ hx).1.ne'

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContinuousAt (reeb H) x :=
  continuousAt_reeb_aux H hH x hx
