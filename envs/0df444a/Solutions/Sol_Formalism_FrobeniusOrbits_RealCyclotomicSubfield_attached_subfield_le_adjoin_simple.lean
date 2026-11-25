-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.attached_subfield_le_adjoin_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:52:09.781802+00:00
-- url     : https://prove2.me/submissions/10a6b398-c5d2-4d9f-b136-5de397ce91f1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_theta_mem_adj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution (ζ : L) : F1 ζ ≤ ℚ⟮ζ⟯ := by
  exact adjoin_simple_le_iff.mpr (theta_mem_adj ζ)
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
