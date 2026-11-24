-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Misc2.int_units_sq_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:44.609659+00:00
-- url     : https://prove2.me/submissions/33ad2198-45dc-442f-a71a-bbd595fe23d3

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
theorem _root_.solution (x : ℤˣ) : (((x : ℤ) : ℂ)) * ((x : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> simp
end Formalism.FrobeniusOrbits.Misc2
