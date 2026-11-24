-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.galE_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:01:12.767431+00:00
-- url     : https://prove2.me/submissions/410ba9cb-e8bf-44bb-9636-cb741b50028c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_one
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_injective

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
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : galE e ζ a b σ = 1 ↔ σ = 1 := by
  constructor
  · intro hs
    exact galE_injective hqd h (hs.trans (galE_one hqd h).symm)
  · rintro rfl
    exact galE_one hqd h
end Formalism.FrobeniusOrbits
