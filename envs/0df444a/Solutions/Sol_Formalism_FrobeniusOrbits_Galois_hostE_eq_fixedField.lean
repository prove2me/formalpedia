-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.hostE_eq_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:24:23.299195+00:00
-- url     : https://prove2.me/submissions/dad5fd77-61ca-41f9-9912-741ac5b890b6

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_le_fixedField
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_fixingSubgroup_hostE_le

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
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    hostE ζ a b = fixedField (Subgroup.zpowers (tau0 hqd h)) := by
  haveI := (layer_galois hqd h).1
  have hfix : (hostE ζ a b).fixingSubgroup = Subgroup.zpowers (tau0 hqd h) :=
    le_antisymm (fixingSubgroup_hostE_le hqd h)
      ((IntermediateField.le_iff_le _ _).1 (hostE_le_fixedField hqd h))
  rw [← hfix, IsGalois.fixedField_fixingSubgroup]
end Formalism.FrobeniusOrbits.Galois
