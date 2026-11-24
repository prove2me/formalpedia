-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_mem_J
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:02.202278+00:00
-- url     : https://prove2.me/submissions/81adc5fb-0b89-4c5f-9536-e5a7a8e1ddf7

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) (r : R) :
    r ∈ unimodUnramUnique_J hR₀ ↔ ∀ c : R, ¬ IsUnit (c * r + star (c * r)) := Iff.rfl
end Formalism.HermitianLatticesTheory
