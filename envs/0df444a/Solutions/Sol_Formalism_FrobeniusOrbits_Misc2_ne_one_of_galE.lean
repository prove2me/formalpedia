-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Misc2.ne_one_of_galE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:28.453578+00:00
-- url     : https://prove2.me/submissions/be59b7b2-c805-400f-b94c-9b090f0f8022

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_galE_one

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
    {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hσ : galE e ζ a b σ ≠ 1) : σ ≠ 1 := by
  rintro rfl
  exact hσ (galE_one hqd h)
end Formalism.FrobeniusOrbits.Misc2
