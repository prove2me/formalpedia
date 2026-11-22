-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.antitone_on
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:53:47.036853+00:00
-- url     : https://prove2.me/submissions/0ab88e38-6afc-40d1-a55c-37f30144051a

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I
namespace Formalism.FourierDecayAlt.P.Interlace
theorem _root_.solution {f : ℕ → ℝ} {k : ℕ} (h : ∀ i, 1 ≤ i → i + 1 ≤ k → f (i + 1) ≤ f i) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → f j ≤ f i := by
  intro i j hi hij hjk
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact (h n (by omega) hjk).trans (ih (by omega))
end Formalism.FourierDecayAlt.P.Interlace
