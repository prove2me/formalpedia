-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfC.cspC_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:09.421829+00:00
-- url     : https://prove2.me/submissions/297207cb-87a4-4667-a749-5774f1b7a3d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfC
open TensorProduct
variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]
namespace Formalism.L2.Pj.CompSplitPfC
theorem _root_.solution (s : S) : algebraMap S (S ⊗[P] FractionRing P) s = s ⊗ₜ (1 : FractionRing P) := rfl
end Formalism.L2.Pj.CompSplitPfC
