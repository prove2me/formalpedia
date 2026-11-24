-- Prove2me | solution 1 for FairSelling.ZeroPrice.GoodSt_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:31.19445+00:00
-- url     : https://prove2.me/submissions/adfffb4c-b58c-4a84-8d5e-c942ee6dd165

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ZeroPrice
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) :
    GoodSt v p ((∅ : Finset (Fin n)), fun _ => (∅ : Finset G)) := by
  refine ⟨fun i _ => rfl, fun i j _ => by simp, fun i hi => absurd hi (by simp), ?_⟩
  intro i hi
  exact absurd hi (by simp)
end FairSelling.ZeroPrice
