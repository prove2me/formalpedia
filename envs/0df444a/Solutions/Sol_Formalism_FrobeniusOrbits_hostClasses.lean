-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostClasses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:46:37.776125+00:00
-- url     : https://prove2.me/submissions/233caf0f-4d0a-4b31-a27b-283190e6cc89

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
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
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Misc Galois
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostClasses := by
  intro e q d hqd L _ _ ζ a b hL p _ hp2 hpq hpd P _ _ σ hσ
  obtain ⟨h1, h2, -⟩ :=
    (((hostFrob_of hostGalois hostGalSpec) e q d hqd L ζ a b hL p hp2 hpq hpd P).2.1 σ).1 hσ
  rw [← h1, ← h2]
  generalize (galE e ζ a b σ).1 = x
  obtain ⟨u1, u2⟩ := x
  rcases Int.units_eq_one_or u1 with rfl | rfl <;> rcases Int.units_eq_one_or u2 with rfl | rfl <;>
    simp [c0, Prod.ext_iff] <;> decide
end Formalism.FrobeniusOrbits
