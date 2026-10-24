-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_one_of_local_scale_deriv_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T09:17:28.852287+00:00
-- url     : https://prove2.me/submissions/75b10ece-08fc-493b-b93a-7454ede743bc

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hcpos : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hdpos : 0 < deriv W (cstar W).toReal) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  let c : ℝ := (cstar W).toReal
  have hc : 0 < c := hcpos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdc : 0 < deriv W c := hdpos
  have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
    simp [scaleDeriv, hcne]
  have hdiv (y : ℝ) :
      divE (W y) (scaleDeriv W c) = W y / deriv W c := by
    simp [hscale, divE]
  have hratio : deriv W c / deriv W c = 1 :=
    div_self (ne_of_gt hdc)
  have hL0raw : HasDerivWithinAt
      (fun y : ℝ => W y / deriv W c)
      (deriv W c / deriv W c) (Icc 0 c) c :=
    ((hWdiff.hasDerivAt.div_const (deriv W c)).hasDerivWithinAt)
  have hL0 : HasDerivWithinAt
      (fun y : ℝ => W y / deriv W c) 1 (Icc 0 c) c := by
    simpa only [hratio] using hL0raw
  have hL : HasDerivWithinAt (vcstar W) 1 (Icc 0 c) c :=
    hL0.congr_of_mem (fun y hy => by
      change 0 ≤ y ∧ y ≤ c at hy
      simp [vcstar, barrierValue, c, not_lt.mpr hy.1, hy.2, hdiv])
      ⟨hc.le, le_rfl⟩
  have hR0 : HasDerivWithinAt
      (fun y : ℝ => y - c + W c / deriv W c) 1 (Ici c) c := by
    simpa using
      (((hasDerivAt_id c).sub_const c).add_const
        (W c / deriv W c)).hasDerivWithinAt
  have hR : HasDerivWithinAt (vcstar W) 1 (Ici c) c :=
    hR0.congr_of_mem (fun y hy => by
      change c ≤ y at hy
      rcases eq_or_lt_of_le hy with rfl | hygt
      · simp [vcstar, barrierValue, c, hc.le, hdiv]
      · have hy0 : 0 < y := hc.trans hygt
        simp [vcstar, barrierValue, c, not_lt.mpr hy0.le,
          not_le.mpr hygt, hdiv]) (by simp)
  have hu := hL.union hR
  rw [Icc_union_Ici_eq_Ici hc.le] at hu
  have hd : HasDerivAt (vcstar W) 1 c :=
    hu.hasDerivAt (Ici_mem_nhds hc)
  change deriv (vcstar W) c = 1
  exact hd.deriv
