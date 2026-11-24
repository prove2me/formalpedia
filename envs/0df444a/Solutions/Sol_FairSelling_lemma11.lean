-- Prove2me | solution 1 for FairSelling.lemma11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:27.03802+00:00
-- url     : https://prove2.me/submissions/b40d0838-a019-4fa3-89e3-8a35bf1f40bd

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Theorems.Thm_FairSelling_lemma11_utility
import Theorems.Thm_FairSelling_SEFX_of_SEFXu


set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFX v p o := by
  obtain ⟨o, hvalid, hshare, hsefx⟩ := lemma11_utility v p rho s H
  exact ⟨o, hvalid, hshare, SEFX_of_SEFXu hsefx⟩
end FairSelling
