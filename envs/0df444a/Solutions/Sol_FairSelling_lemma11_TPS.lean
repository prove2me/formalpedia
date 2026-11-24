-- Prove2me | solution 1 for FairSelling.lemma11_TPS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:57.834923+00:00
-- url     : https://prove2.me/submissions/34a52d48-497a-4a0f-87e0-fa67626ac657

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Theorems.Thm_FairSelling_lemma11

set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o :=
  lemma11 v p rho (fun i => TPS n (v i) p) H
end FairSelling
