-- Prove2me | solution 1 for AvramDividend.Classical.drawdown_prepeak_exit_event_inclusions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T05:56:30.090724+00:00
-- url     : https://prove2.me/submissions/87d91a8b-109b-4397-8f06-cd007b8736f3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Theorems.Thm_AvramDividend_Classical_drawdown_strict_exit_strip_of_sup_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {T : Type*} (I : Set T) (S X : T → ℝ) (a h : ℝ)
    (hSup : ∀ t ∈ I, 0 ≤ S t ∧ S t ≤ h) :
    {t : T | t ∈ I ∧ X t < -a} ⊆
      {t : T | t ∈ I ∧ a < S t - X t} ∧
    {t : T | t ∈ I ∧ a < S t - X t} ⊆
      {t : T | t ∈ I ∧ X t < h - a} := by
  constructor
  · intro t ht
    have hS := hSup t ht.1
    have hsandwich :=
      AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds
        a h (S t) (X t) hS.1 hS.2
    exact ⟨ht.1, hsandwich.1 ht.2⟩
  · intro t ht
    have hS := hSup t ht.1
    have hsandwich :=
      AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds
        a h (S t) (X t) hS.1 hS.2
    exact ⟨ht.1, hsandwich.2.1 ht.2⟩
