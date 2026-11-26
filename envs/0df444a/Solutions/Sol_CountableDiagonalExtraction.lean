-- Prove2me | solution 1 for CountableDiagonalExtraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:20.842056+00:00
-- url     : https://prove2.me/submissions/4122a6f0-0a96-448e-8941-b02a1c8999e9

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_CountableDiagonalExtraction

set_option autoImplicit false
open Filter Topology
theorem _root_.solution
    (a : ℕ → ℕ → ℕ → ℝ) (A : ℕ → ℝ)
    (h : ∀ j l, Tendsto (a j l) atTop (nhds (A j))) :
    ∃ N : ℕ → ℕ, StrictMono N ∧
      ∀ j, Tendsto (fun l => a j l (N l)) atTop (nhds (A j)) := by
-- BODY
  classical
  have step : ∀ l : ℕ, ∃ M : ℕ, ∀ j ≤ l, ∀ n ≥ M, |a j l n - A j| < 1 / (l + 1 : ℝ) := by
    intro l
    have hpos : (0:ℝ) < 1 / (l + 1 : ℝ) := by positivity
    have : ∀ j, ∃ M : ℕ, ∀ n ≥ M, |a j l n - A j| < 1 / (l + 1 : ℝ) := by
      intro j
      have := (h j l).eventually (eventually_abs_sub_lt (A j) hpos)
      simpa [eventually_atTop] using this
    choose M hM using this
    refine ⟨(Finset.range (l+1)).sup M, fun j hj n hn => hM j n (le_trans ?_ hn)⟩
    exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  choose M hM using step
  let N : ℕ → ℕ := fun l => Nat.rec (M 0) (fun l ih => max (ih + 1) (M (l+1))) l
  have hNM : ∀ l, M l ≤ N l := by
    intro l; cases l with
    | zero => exact le_refl _
    | succ k => exact le_max_right _ _
  have hmono : StrictMono N := strictMono_nat_of_lt_succ (fun l => by
    show N l < max (N l + 1) (M (l+1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
  refine ⟨N, hmono, fun j => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt (1/ε)
  refine ⟨max j L, fun l hl => ?_⟩
  have hjl : j ≤ l := le_trans (le_max_left _ _) hl
  have hLl : L ≤ l := le_trans (le_max_right _ _) hl
  have := hM l j hjl (N l) (hNM l)
  have hbound : 1 / (l + 1 : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : (1:ℝ)/ε < (l:ℝ) + 1 := lt_of_lt_of_le hL (by exact_mod_cast Nat.le_succ_of_le hLl)
    rw [div_lt_iff₀ hε] at h1
    linarith
  rw [Real.dist_eq]
  exact lt_trans this hbound
