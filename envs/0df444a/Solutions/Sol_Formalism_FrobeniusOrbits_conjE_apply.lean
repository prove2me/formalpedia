-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.conjE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:20.030847+00:00
-- url     : https://prove2.me/submissions/36a7a0ca-eb24-4d02-ba3d-7bc667f3daec

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_conjE
import Theorems.Thm_Formalism_FrobeniusOrbits_hostConj_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois


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
    (φ : hostE ζ a b →+* ℂ) (x : hostE ζ a b) :
    φ (conjE hqd h x) = starRingEnd ℂ (φ x) :=
  ((hostConj_of hostGalois hostGalSpec e q d hqd L ζ a b h).2 φ (conjE hqd h)).2
    (galE_conjE hqd h) x
end Formalism.FrobeniusOrbits
