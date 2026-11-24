-- Prove2me | solution 1 for FairSelling.lemma11_TPS_utility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:39:40.76793+00:00
-- url     : https://prove2.me/submissions/9f4573ca-b8ff-4c5e-b0fb-ccf499278942

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Theorems.Thm_FairSelling_lemma11_utility

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
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFXu v p o :=
  lemma11_utility v p rho (fun i => TPS n (v i) p) H
end FairSelling
