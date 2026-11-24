-- Prove2me | solution 1 for FairSelling.money_le_proceeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:04.835062+00:00
-- url     : https://prove2.me/submissions/54f0dab8-70d3-4260-8611-61ebabb29456

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven

set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution {p : G → ℝ} {o : Outcome G n} (h : o.Valid p) (j : Fin n) :
    o.money j ≤ ∑ g ∈ o.sold, p g := by
  have h1 : o.money j ≤ ∑ k, o.money k :=
    Finset.single_le_sum (f := o.money) (fun k _ => h.2.2.1 k) (Finset.mem_univ j)
  linarith [h.2.2.2]
end FairSelling
