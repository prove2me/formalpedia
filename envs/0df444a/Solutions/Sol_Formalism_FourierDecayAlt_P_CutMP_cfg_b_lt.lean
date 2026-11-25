-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.cfg_b_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:53.457513+00:00
-- url     : https://prove2.me/submissions/08fa7da7-bef3-43df-b259-e54173433d28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
variable (c : Sz.Cfg)
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution (hok : c.Ok) : ∀ {j j' : ℕ}, 1 ≤ j → j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j j' hj hjj' hj'm
  induction j' with
  | zero => omega
  | succ n ih =>
    have hg := hok.hgap n (by omega) (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjj' with h | h
    · have := ih h (by omega)
      linarith
    · subst h
      linarith
end Formalism.FourierDecayAlt.P.CutMP
