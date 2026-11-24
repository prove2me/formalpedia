-- Prove2me | solution 1 for FairSelling.vbarSum_sdiff_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:55.115409+00:00
-- url     : https://prove2.me/submissions/9f467c91-f0ca-4514-943e-c25d31605361

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution {vi p : G → ℝ} {A : Finset G} {g : G} (hg : g ∈ A) :
    vbarSum vi p A = vbarSum vi p (A \ {g}) + vbar vi p g := by
  classical
  have hA : A = insert g (A \ {g}) := by
    ext x
    by_cases hx : x = g <;> simp [hx, hg]
  rw [vbarSum, vbarSum, hA, Finset.sum_insert (by simp)]
  simp [add_comm]
end FairSelling
