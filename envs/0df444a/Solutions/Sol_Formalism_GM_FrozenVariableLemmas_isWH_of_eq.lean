-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.isWH_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:44.7638+00:00
-- url     : https://prove2.me/submissions/f0e3cb39-d9dc-46fc-8ccc-dc8996578d19

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution {σ R : Type} [CommSemiring R] {w : σ → ℕ} {φ : MvPolynomial σ R} {a b : ℕ}
    (h : IsWeightedHomogeneous w φ a) (e : a = b) : IsWeightedHomogeneous w φ b := by
  subst e
  exact h
end Formalism.GM.FrozenVariableLemmas
