-- Prove2me | solution 1 for AvramDividend.Classical.causal_zero_extension_continuous_of_Ici_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:53:58.554452+00:00
-- url     : https://prove2.me/submissions/5da209c9-ac2e-4b41-8031-8c8a106fd38c

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Algebra.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (V : ℝ → ℝ)
    (hV : ContinuousOn V (Ici (0 : ℝ)))
    (hV0 : V 0 = 0) :
    Continuous ((Ioi (0 : ℝ)).indicator V) := by
  let F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator V
  have hpos : ∀ x ∈ Ici (0 : ℝ), F x = V x := by
    intro x hx
    change (0 : ℝ) ≤ x at hx
    rcases eq_or_lt_of_le hx with heq | hgt
    · subst x
      simp [F, hV0]
    · simp [F, hgt]
  have hneg : ∀ x ∈ Iic (0 : ℝ), F x = 0 := by
    intro x hx
    change x ≤ (0 : ℝ) at hx
    have hn : x ∉ Ioi (0 : ℝ) := by
      intro h
      change (0 : ℝ) < x at h
      exact (not_lt_of_ge hx h)
    simp [F, hn]
  have hcpos : ContinuousOn F (Ici (0 : ℝ)) :=
    hV.congr hpos
  have hcneg : ContinuousOn F (Iic (0 : ℝ)) :=
    continuousOn_const.congr hneg
  have hcunion : ContinuousOn F (Ici (0 : ℝ) ∪ Iic (0 : ℝ)) :=
    hcpos.union_of_isClosed hcneg isClosed_Ici isClosed_Iic
  have huniv : Ici (0 : ℝ) ∪ Iic (0 : ℝ) = Set.univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 x
  have hc : ContinuousOn F Set.univ := by
    simpa only [huniv] using hcunion
  exact continuousOn_univ.mp hc
