-- Prove2me | solution 1 for AvramDividend.Classical.chat03_strict_exit_mesh_approximation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:25:14.25443+00:00
-- url     : https://prove2.me/submissions/aa07d980-a0f6-477b-bd19-7d9147e2af6f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
An approximation lemma for the infimum of the strict two-sided exit set.
Do not assume the first passage infimum itself is a strict exit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < τ + ε ∧
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) := by
  classical
  let S : Set ℝ≥0 :=
    {t | X.X t ω < lower ∨ upper < X.X t ω}
  change IsGLB S τ at hτ
  have hwitness :
      ∃ t : ℝ≥0, τ ≤ t ∧ t < τ + ε ∧ t ∈ S := by
    by_contra hnone
    have hb : τ + ε ∈ lowerBounds S := by
      intro t ht
      by_contra hnot
      have hlt : t < τ + ε := lt_of_not_ge hnot
      exact hnone ⟨t, hτ.1 ht, hlt, ht⟩
    have htoo : τ + ε ≤ τ := hτ.2 hb
    exact (not_le_of_gt (lt_add_of_pos_right τ hε)) htoo
  obtain ⟨t, hτt, htε, htS⟩ := hwitness
  obtain ⟨u, htu, hright⟩ :=
    chat03_strict_exit_right_interval X ω t lower upper htS
  have hmin : t < min u (τ + ε) := lt_min htu htε
  obtain ⟨v, htv, hv⟩ := exists_between hmin
  have hvu : v < u := (lt_min_iff.mp hv).1
  have hvε : v < τ + ε := (lt_min_iff.mp hv).2
  let δ : ℝ≥0 := v - t
  have hδ : 0 < δ := tsub_pos_iff_lt.mpr htv
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨hlo, hhi⟩ :=
    chat03_nnreal_grid_ceiling_bracket t h hh
  have htplus : t + h < v := by
    calc
      t + h < t + (v - t) := by
        simpa only [δ, add_comm] using (add_lt_add_left hhd t)
      _ = v := add_tsub_cancel_of_le htv.le
  let k : ℕ := Nat.ceil (t / h)
  refine ⟨k, hτt.trans hlo, ?_, ?_⟩
  · exact hhi.trans (htplus.trans hvε)
  · exact hright _ hlo (hhi.trans (htplus.trans hvu))
