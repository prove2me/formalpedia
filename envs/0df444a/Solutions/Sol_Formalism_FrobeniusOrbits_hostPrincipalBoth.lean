-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostPrincipalBoth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:55.141395+00:00
-- url     : https://prove2.me/submissions/33a32014-7097-4cb5-892e-1aeea2db534b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDiffSupport
import Theorems.Thm_Formalism_FrobeniusOrbits_hostPrincipal

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
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostDiffSupport ∧ HostPrincipal := ⟨hostDiffSupport, hostPrincipal⟩
end Formalism.FrobeniusOrbits
