-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Eq.J.Neg.norm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:13:36.832026+00:00
-- url     : https://prove2.me/submissions/f78b9544-b96c-4bcc-81b0-d18c26b5db89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq.J.Neg
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
theorem _root_.solution (p : ℕ) [Fact p.Prime] (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : ‖(k : ℤ_[p])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  exact h ((PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := k)).1 (not_le.1 hlt))
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
