-- Prove2me | solution 1 for Formalism.HC.Frame.ofEquiv_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:51.783011+00:00
-- url     : https://prove2.me/submissions/e8d72665-03cf-49e0-8419-ac8cc440b3dd

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
namespace Formalism.HC.Frame
theorem _root_.solution : (ofEquiv e ε h' hs a' hk).n0 = addOrderOf a' := by
  show addOrderOf (ofEquiv e ε h' hs a' hk).a0 = _
  conv_rhs => rw [← ofEquiv_generator e ε h' hs a' hk]
  exact (addOrderOf_injective (ofEquivIso e ε h' hs a' hk).toAddMonoidHom
    (ofEquivIso e ε h' hs a' hk).injective _).symm
end Formalism.HC.Frame
