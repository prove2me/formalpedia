-- Prove2me | solution 1 for Formalism.HC.Frame.ofEquiv_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:55:12.437064+00:00
-- url     : https://prove2.me/submissions/aac74c12-af73-413c-9ff7-99ed745df6a4

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.HC.Frame
variable {A' : Type} [AddCommGroup A'] (e : ℕ) {n : ℕ} (ε : Idx n ≃ A') (h' : A' →+ Additive (HGrp e))
  (hs : Function.Surjective h') (a' : A') (hk : ∀ k : ℤ, h' (k • a') = 0 → k • a' = 0)
namespace Formalism.HC.Frame
theorem _root_.solution (t : (ofEquiv e ε h' hs a' hk).A) :
    (ofEquiv e ε h' hs a' hk).h t = h' (ofEquivIso e ε h' hs a' hk t) := rfl
end Formalism.HC.Frame
