-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.conjE_mem_hostF_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:04.707442+00:00
-- url     : https://prove2.me/submissions/180d7b28-1e8f-49a2-920d-47e927236ef2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_conjE
import Theorems.Thm_Formalism_FrobeniusOrbits_eq_conjE_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_hostReal_at

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
    (x : hostE ζ a b) : x ∈ hostF ζ a b ↔ conjE hqd h x = x := by
  rw [((hostReal_at hqd h).2 x).1]
  constructor
  · intro hx
    exact hx _ (galE_conjE hqd h)
  · intro hx σ hσ
    rw [(eq_conjE_iff hqd h σ).2 hσ]
    exact hx
end Formalism.FrobeniusOrbits
