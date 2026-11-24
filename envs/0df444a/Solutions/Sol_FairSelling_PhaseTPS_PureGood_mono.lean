-- Prove2me | solution 1 for FairSelling.PhaseTPS.PureGood.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:31.670195+00:00
-- url     : https://prove2.me/submissions/a2578a3c-1dfa-47ad-9701-7c87c901e41d

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.PhaseTPS
namespace PureGood
theorem _root_.solution {v : Fin n → G → ℝ} {p : G → ℝ} {A B : Finset (Fin n)} (hAB : A ⊆ B)
    {g : G} (h : PureGood v p A g) : PureGood v p B g :=
  fun j hj => h j (fun hjA => hj (hAB hjA))
end PureGood
end FairSelling.PhaseTPS
