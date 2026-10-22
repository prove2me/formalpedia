-- Prove2me | solution 1 for GDGen3.decreasing_sequence_tail
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:46:36.774884+00:00
-- url     : https://prove2.me/submissions/51eb2abd-eb41-414d-aa2c-67291e5dac6a

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (q : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → q (i + 1) ≤ q i) (i : ℕ) (hi : i ≤ N) : q N ≤ q i := by
  have hchain : ∀ j, i ≤ j → j ≤ N → q j ≤ q i := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro h; exact le_rfl
    | succ j hij ih =>
      intro hjN
      exact le_trans (hstep j (by omega)) (ih (by omega))
  exact hchain N hi le_rfl
