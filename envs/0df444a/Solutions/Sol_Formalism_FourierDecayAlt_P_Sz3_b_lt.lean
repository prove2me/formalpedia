-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.b_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:38.455069+00:00
-- url     : https://prove2.me/submissions/4b5642a1-e9d8-46fc-b1b9-187449914fa1

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) :
    ∀ j' : ℕ, j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j' hjj'
  induction j', hjj' using Nat.le_induction with
  | base =>
    intro h
    have := hc.hgap j hj (by omega)
    linarith
  | succ n hn ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hc.hgap n (by omega) (by omega)
    linarith
end Formalism.FourierDecayAlt.P.Sz3
