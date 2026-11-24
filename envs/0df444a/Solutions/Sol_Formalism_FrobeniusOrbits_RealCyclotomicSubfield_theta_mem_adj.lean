-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.theta_mem_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:41.364859+00:00
-- url     : https://prove2.me/submissions/0a36f004-fd85-49bd-b743-3fd9b70d2dc1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield

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
theorem _root_.solution (ζ : L) : ζ + ζ⁻¹ ∈ ℚ⟮ζ⟯ := by
  exact add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ))
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
