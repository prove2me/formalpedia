-- Prove2me | solution 1 for FairSelling.lemma11_TPS_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:58.502554+00:00
-- url     : https://prove2.me/submissions/3dc0795b-eb8b-4c40-bb63-0df084b590ef

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Theorems.Thm_FairSelling_lemma11_strict
import Theorems.Thm_FairSelling_SEFX_of_SEFXs


set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFXs v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  obtain ⟨o, hvalid, hshare, hsefx⟩ := lemma11_strict v p rho (fun i => TPS n (v i) p) H
  exact ⟨o, hvalid, hshare, SEFX_of_SEFXs hvalid hsefx⟩
end FairSelling
