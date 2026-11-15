-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a374_finite_masked_Young_half_epsilon_energy_cross_factor_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:24:30.198205+00:00
-- url     : https://prove2.me/submissions/825dbc2f-546f-4e4e-bb4e-1db28cb926b3

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {ι : Type*} (S : Finset ι) (A : ι → Prop) [DecidablePred A]
    (r z : ι → ℝ) (ε M q Δ L : ℝ) (hε : 0 < ε) :
    (∑ i ∈ S, if A i then ((ε / 2) + (ε / 2)) * (r i)^2 else 0) +
    (∑ i ∈ S, if A i then M / 2 * |(r i)^2-(z i)^2| else 0) +
      (S.card : ℝ) * ((q*Δ*L)^2/(4*(ε/2))) =
    ε * (∑ i ∈ S, if A i then (r i)^2 else 0) +
    (M/2) * (∑ i ∈ S, if A i then |(r i)^2-(z i)^2| else 0) +
      (S.card : ℝ) * ((q*Δ*L)^2/(2*ε)) := by
  classical
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hDen : 2 * ε ≠ 0 := by positivity
  have hY : ((q*Δ*L)^2/(4*(ε/2))) =
      ((q*Δ*L)^2/(2*ε)) := by
    field_simp
    ring
  rw [hY]
  have hFirst :
      (∑ i ∈ S, if A i then ((ε / 2)+(ε / 2))*(r i)^2 else 0) =
      ε * (∑ i ∈ S, if A i then (r i)^2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hSecond :
      (∑ i ∈ S, if A i then M/2*|(r i)^2-(z i)^2| else 0) =
      (M/2)*(∑ i ∈ S, if A i then |(r i)^2-(z i)^2| else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [hFirst,hSecond]
