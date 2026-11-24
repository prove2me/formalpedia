-- Prove2me | solution 1 for FairSelling.lemma11_u
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:19.092929+00:00
-- url     : https://prove2.me/submissions/7c63768d-f5dd-42f4-83c0-2d347f87e48b

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Theorems.Thm_FairSelling_lemma11_utility_u
import Theorems.Thm_FairSelling_SEFX_of_SEFXu


set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFXu v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFX v p o := by
  obtain ⟨o, hvalid, hshare, hsefx⟩ := lemma11_utility_u v p rho s H
  exact ⟨o, hvalid, hshare, SEFX_of_SEFXu hsefx⟩
end FairSelling
