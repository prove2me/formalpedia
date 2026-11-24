-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Misc2.conjHom_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:43.631285+00:00
-- url     : https://prove2.me/submissions/b59ccf01-5f6e-471b-8acc-726b7b97f54e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup

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
open Misc2
open Formalism.FrobeniusOrbits.Misc2
namespace Formalism.FrobeniusOrbits.Misc2
theorem _root_.solution {G : Type*} [Group G] (χ : G →* ℂˣ) : conjHom χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [conjHom, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.one_apply] at this
    have := congrArg (starRingEnd ℂ) this
    simpa using this
  · rintro rfl
    ext g
    simp [conjHom]
end Formalism.FrobeniusOrbits.Misc2
