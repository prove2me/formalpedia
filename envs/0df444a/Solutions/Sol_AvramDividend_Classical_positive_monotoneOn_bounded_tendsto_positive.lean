-- Prove2me | solution 1 for AvramDividend.Classical.positive_monotoneOn_bounded_tendsto_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:36:53.592486+00:00
-- url     : https://prove2.me/submissions/d33b099c-9667-4682-8590-fda658474c29

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology

theorem solution
    (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hmono : MonotoneOn V (Ioi (0 : ℝ)))
    (hupper : ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (𝓝 L) := by
  obtain ⟨C, hC⟩ := hupper
  let f : ℝ → ℝ := fun x => V (max x 1)
  have hmaxpos (x : ℝ) : 0 < max x 1 := by
    have h : (1 : ℝ) ≤ max x 1 := le_max_right x 1
    linarith
  have hmonof : Monotone f := by
    intro x y hxy
    exact hmono (Set.mem_Ioi.mpr (hmaxpos x))
      (Set.mem_Ioi.mpr (hmaxpos y))
      (max_le_max hxy (le_refl (1 : ℝ)))
  have hfupper : ∀ x : ℝ, f x ≤ C :=
    fun x => hC (max x 1) (hmaxpos x)
  obtain hdiv | ⟨L, hL⟩ := tendsto_atTop_of_monotone hmonof
  · have hev : ∀ᶠ x : ℝ in atTop, C + 1 ≤ f x :=
      (tendsto_atTop.1 hdiv (C + 1))
    obtain ⟨x, hx⟩ := hev.exists
    linarith [hfupper x]
  · have hlow : ∀ x : ℝ, V 1 ≤ f x := by
      intro x
      exact hmono (Set.mem_Ioi.mpr (by norm_num))
        (Set.mem_Ioi.mpr (hmaxpos x)) (le_max_right x 1)
    have hlim : V 1 ≤ L :=
      ge_of_tendsto hL (Filter.Eventually.of_forall hlow)
    have hLpos : 0 < L := lt_of_lt_of_le (hpos 1 (by norm_num)) hlim
    have hEq : f =ᶠ[atTop] V := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      simp only [f, max_eq_left hx]
    exact ⟨L, hLpos, hL.congr' hEq⟩
