-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.top_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:34:17.251447+00:00
-- url     : https://prove2.me/submissions/6985e51a-15a8-484d-9606-e0ebaab43f1c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec

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
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution (m : ℕ) [NeZero m] : IntermediateField.adjoin ℚ ({z m} : Set (Cyc m)) = ⊤ := by
  exact IntermediateField.adjoin_eq_top_of_algebra ℚ _
   (IsCyclotomicExtension.adjoin_primitive_root_eq_top (z_spec m))
end Formalism.FrobeniusOrbits.Cond
