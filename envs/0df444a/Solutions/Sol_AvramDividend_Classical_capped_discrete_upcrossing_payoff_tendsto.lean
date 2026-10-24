-- Prove2me | solution 1 for AvramDividend.Classical.capped_discrete_upcrossing_payoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:19:15.313409+00:00
-- url     : https://prove2.me/submissions/203bc9f9-d467-4c30-af3d-9e07f38549d3

import Mathlib.Probability.Process.HittingTime
import Mathlib.Data.Nat.Find
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_monotone_grid_inf_first_hit_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    (u : ℕ → ℝ) (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (z q : ℝ) [DecidablePred (fun k : ℕ => z < u k)] :
    Tendsto
      (fun m : ℕ =>
        let K := hittingBtwn (fun k (_ : Unit) => u k) (Ioi z) 0 m ()
        if z < u K then ENNReal.ofReal
          (Real.exp (-(q * (clock K : ℝ)))) else 0) atTop
      (𝓝 (let T : ℝ≥0∞ :=
        ⨅ k : ℕ, if z < u k then (clock k : ℝ≥0∞) else ∞
        if T < ∞ then ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal T))) else 0)) := by
  classical
  let v : ℕ → Unit → ℝ := fun k _ => u k
  let T : ℝ≥0∞ := ⨅ k : ℕ,
    if z < u k then (clock k : ℝ≥0∞) else ∞
  change Tendsto
    (fun m : ℕ =>
      if z < u (hittingBtwn v (Ioi z) 0 m ()) then
        ENNReal.ofReal (Real.exp
          (-(q * (clock (hittingBtwn v (Ioi z) 0 m ()) : ℝ))))
      else 0)
    atTop
    (𝓝 (if T < ∞ then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal T)))
      else 0))
  by_cases h : ∃ k : ℕ, z < u k
  · let j : ℕ := Nat.find h
    have hj : z < u j := Nat.find_spec h
    have hex : ∃ k ∈ Set.Icc 0 j, v k () ∈ Ioi z := by
      exact ⟨j, by simp, hj⟩
    have hhit : z < u (hittingBtwn v (Ioi z) 0 j ()) := by
      exact hittingBtwn_mem_set
        (u := v) (s := Ioi z) (n := 0) (m := j) (ω := ()) hex
    have hmin : j ≤ hittingBtwn v (Ioi z) 0 j () :=
      Nat.find_le (h := h) hhit
    have hmax : hittingBtwn v (Ioi z) 0 j () ≤ j :=
      hittingBtwn_le (u := v) (s := Ioi z) (n := 0) (m := j) ()
    have heq : hittingBtwn v (Ioi z) 0 j () = j :=
      le_antisymm hmax hmin
    have hstable (m : ℕ) (hm : j ≤ m) :
        hittingBtwn v (Ioi z) 0 m () = j := by
      have hsame : hittingBtwn v (Ioi z) 0 j () =
          hittingBtwn v (Ioi z) 0 m () :=
        hittingBtwn_eq_hittingBtwn_of_exists
          (u := v) (s := Ioi z) (n := 0) (ω := ()) hm hex
      exact hsame.symm.trans heq
    have hT : T = (clock j : ℝ≥0∞) := by
      simpa only [T, Set.mem_Ioi, j] using
        (monotone_grid_inf_first_hit_time u (Ioi z) clock hc h)
    have hTfin : T < ∞ := by rw [hT]; exact ENNReal.coe_lt_top
    have hTreal : ENNReal.toReal T = (clock j : ℝ) := by
      rw [hT]
      simp
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Filter.eventually_ge_atTop j] with m hm
    rw [hstable m hm]
    simp [hj, hTfin, hTreal]
  · have hn : ∀ k : ℕ, ¬ z < u k := by
      simpa only [not_exists] using h
    have hT : T = ∞ := by simp [T, hn]
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [] with m
    simp [hT, hn (hittingBtwn v (Ioi z) 0 m ())]
