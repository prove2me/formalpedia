-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.z_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:14:17.842695+00:00
-- url     : https://prove2.me/submissions/a8d3f6ed-bcc0-4bf3-a425-7106015cb980

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq

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
theorem _root_.solution (m : ℕ) [NeZero m] : IsPrimitiveRoot (z m) m := by
  exact IsCyclotomicExtension.zeta_spec m ℚ (Cyc m)
end Formalism.FrobeniusOrbits.Cond
