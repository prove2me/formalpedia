-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.bE_mem_KinE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:43:30.463726+00:00
-- url     : https://prove2.me/submissions/f738be80-1d87-4199-bd13-9da2c93e3746

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (ζ a b : L) : bE ζ a b ∈ KinE ζ a b := by
  first
  | exact IntermediateField.mem_adjoin_simple_self ℚ (bE ζ a b)
  | (unfold KinE; exact IntermediateField.mem_adjoin_simple_self ℚ _)
end Formalism.FrobeniusOrbits.Principal
