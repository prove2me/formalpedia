-- Prove2me | solution 1 for FirstPassageLinearTransport.bernoulliWordWeight_rev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:19.876963+00:00
-- url     : https://prove2.me/submissions/b866f08a-1184-4652-bbd9-bc9b1a6b6dba

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} {a : ℕ} (w : Fin a → Bool) :
    bernoulliWordWeight p (fun i => w (Fin.rev i)) =
      bernoulliWordWeight p w := by
  unfold bernoulliWordWeight
  exact Equiv.prod_comp Fin.revPerm
    (fun i => if w i then p else 1 - p)
end FirstPassageLinearTransport
