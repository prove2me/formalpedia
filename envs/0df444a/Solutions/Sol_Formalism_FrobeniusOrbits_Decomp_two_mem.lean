-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.two_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:15:50.799232+00:00
-- url     : https://prove2.me/submissions/d829a8b2-08df-4f28-a41a-a49730902c89

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M))
    [P.LiesOver (span {(2 : ℤ)})] : (2 : 𝓞 M) ∈ P := by
  have h2 : (2 : ℤ) ∈ P.under ℤ := by
    rw [← (Ideal.LiesOver.over : span {(2 : ℤ)} = P.under ℤ)]
    exact Ideal.mem_span_singleton_self 2
  simpa using Ideal.mem_comap.mp h2
end Formalism.FrobeniusOrbits.Decomp
