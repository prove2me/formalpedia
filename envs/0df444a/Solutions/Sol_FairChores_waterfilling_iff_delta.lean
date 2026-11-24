-- Prove2me | solution 1 for FairChores.waterfilling_iff_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:53:20.872705+00:00
-- url     : https://prove2.me/submissions/755be25d-20e4-4269-a241-8afae0550a6f

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_cbarSum_sdiff_singleton

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T]
namespace FairChores
theorem _root_.solution {Bi Bj : Finset T} {t : T} (ht : t ∈ Bi) :
    (cbarSum ci p (Bi \ {t}) + cbarSum ci p Bj + p t) / 2 ≥ cbarSum ci p Bi ↔
      p t - cbar ci p t ≥ cbarSum ci p Bi - cbarSum ci p Bj := by
  rw [cbarSum_sdiff_singleton (ci := ci) (p := p) ht]
  constructor <;> intro h <;> linarith
end FairChores
