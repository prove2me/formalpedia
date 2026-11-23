-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.frob_comp_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:27.0405+00:00
-- url     : https://prove2.me/submissions/adccfff1-ae10-4628-acea-328162097f02

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution : (frobenius (Fbar g) g).comp (algebraMap (ZMod g) (Fbar g)) =
    algebraMap (ZMod g) (Fbar g) := RingHom.ext_zmod _ _
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
