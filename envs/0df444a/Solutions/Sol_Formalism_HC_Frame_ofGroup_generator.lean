-- Prove2me | solution 1 for Formalism.HC.Frame.ofGroup_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:55:22.662834+00:00
-- url     : https://prove2.me/submissions/ec4af9e9-8f16-43e0-8427-900c76950966

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_Frame_ofEquiv_generator

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
variable [Fintype A']
namespace Formalism.HC.Frame
theorem _root_.solution : ofGroupIso e h' hs a' hk (ofGroup e h' hs a' hk).a0 = a' :=
  ofEquiv_generator e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk
end Formalism.HC.Frame
