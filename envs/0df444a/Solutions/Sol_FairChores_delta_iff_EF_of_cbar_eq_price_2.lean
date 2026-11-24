-- Prove2me | solution 2 for FairChores.delta_iff_EF_of_cbar_eq_price
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:53:21.756946+00:00
-- url     : https://prove2.me/submissions/318bcc93-49c9-489b-9f92-e46e7ecebd5e

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution {Bi Bj : Finset T} {t : T} (h : cbar ci p t = p t) :
    (p t - cbar ci p t ≥ cbarSum ci p Bi - cbarSum ci p Bj) ↔
      cbarSum ci p Bi ≤ cbarSum ci p Bj := by
  rw [h]
  constructor <;> intro h' <;> linarith
end FairChores
