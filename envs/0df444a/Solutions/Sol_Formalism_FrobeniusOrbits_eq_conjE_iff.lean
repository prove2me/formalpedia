-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.eq_conjE_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:01:09.704854+00:00
-- url     : https://prove2.me/submissions/39826d05-0b55-43ab-8c37-74bc392ae4c2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_injective
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_conjE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : σ = conjE hqd h ↔ galE e ζ a b σ = cc e := by
  constructor
  · rintro rfl
    exact galE_conjE hqd h
  · intro hs
    exact galE_injective hqd h (hs.trans (galE_conjE hqd h).symm)
end Formalism.FrobeniusOrbits
