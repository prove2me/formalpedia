-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Misc2.galE_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:46:36.206573+00:00
-- url     : https://prove2.me/submissions/9510d934-c66f-469d-b765-25e16d33764f

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Misc2
namespace Formalism.FrobeniusOrbits.Misc2
theorem _root_.solution {e q d : ℕ} (hqd : HypOdd q d) {L : Type} [Field L] [NumberField L]
    {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (1 : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) = 1 := by
  obtain ⟨-, -, hmulE, -⟩ := hostGalois e q d hqd L ζ a b h
  have := hmulE 1 1
  rw [mul_one] at this
  exact (mul_eq_left.mp this.symm)
end Formalism.FrobeniusOrbits.Misc2
