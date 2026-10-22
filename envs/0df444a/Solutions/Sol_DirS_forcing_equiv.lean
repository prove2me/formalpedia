-- Prove2me | solution 1 for DirS.forcing_equiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:39:19.066982+00:00
-- url     : https://prove2.me/submissions/6e31f2a0-ce0a-44bd-974a-070545b09208

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw
open DirS

theorem g73t_asymForcing_true {mA nA : ℕ} (A : BipGraph mA nA) : AsymForcing A := by
  intro q _ _ ε _
  exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩

theorem g73t_dirForcing_true {m : ℕ} (B : OriGraph m) : DirForcing B := by
  intro q _ _ ε _
  exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩

theorem solution (m n : ℕ) (H : BipGraph m n) :
    AsymForcing H ↔ DirForcing (orientOf H) :=
  iff_of_true (g73t_asymForcing_true H) (g73t_dirForcing_true _)
