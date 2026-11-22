-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz7.prodb_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:54.515999+00:00
-- url     : https://prove2.me/submissions/d82027aa-b955-4882-a5f2-f08551c5bbc1

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
private lemma one_le_b_of_ok (c : Cfg) (h : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
  intro j
  induction j with
  | zero => intro h1; omega
  | succ n ih =>
    intro h1 h2
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using h.hb1
    · have e1 := ih hn (by omega)
      have e2 := h.hgap n hn (by omega)
      linarith
end Formalism.FourierDecayAlt.P.Sz7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz7
theorem _root_.solution (c : Cfg) (h : c.Ok) : 0 < c.prodb := by
  unfold Cfg.prodb
  exact Finset.prod_pos (fun j hj => by
    rw [Finset.mem_Icc] at hj
    linarith [one_le_b_of_ok c h j hj.1 hj.2])
end Formalism.FourierDecayAlt.P.Sz7
