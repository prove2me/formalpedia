-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:30.194052+00:00
-- url     : https://prove2.me/submissions/fb759f49-801b-4c66-91de-ab4bb6227e2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_all

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
theorem _root_.solution (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) (hm : 0 < m) :
    ∃ α β γ δ s : ℤ, (α ^ 2 + q * β ^ 2) * (γ ^ 2 + d * δ ^ 2) = -1 + m * s := by
  obtain ⟨α, β, γ, δ, h⟩ := rep_all q d hq hd hq8 hqd m hm
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective α
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective β
  obtain ⟨c, rfl⟩ := ZMod.intCast_surjective γ
  obtain ⟨e, rfl⟩ := ZMod.intCast_surjective δ
  have hdvd : (m : ℤ) ∣ (a ^ 2 + q * b ^ 2) * (c ^ 2 + d * e ^ 2) + 1 := by
    rw [← CharP.intCast_eq_zero_iff (ZMod m) m]
    push_cast
    linear_combination h
  obtain ⟨s, hs⟩ := hdvd
  exact ⟨a, b, c, e, s, by linear_combination hs⟩
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
