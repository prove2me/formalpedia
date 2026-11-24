-- Prove2me | solution 1 for Formalism.CohomologicalDescent.lw_det_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:29.38293+00:00
-- url     : https://prove2.me/submissions/9d6f045a-63ff-4414-8ea8-90baac951b2c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLW
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (s : m) (hs : ∀ j, b j = b s → j = s) :
    (M.toSquareBlock b (b s)).det = M s s := by
  let _ : Unique {a // b a = b s} :=
    { default := ⟨s, rfl⟩
      uniq := fun j => Subtype.ext (hs j.1 j.2) }
  rw [Matrix.det_unique]
  rfl
end Formalism.CohomologicalDescent
