-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_hermFix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:35.380184+00:00
-- url     : https://prove2.me/submissions/d93dd04b-1f7d-4543-bcb0-1e2ee17cdfdf

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
theorem _root_.solution {ι : Type} (A : Matrix ι ι R) (hA : Aᴴ = A) (i j : ι) :
    star (A j i) = A i j := by
  simpa [conjTranspose_apply] using congrFun (congrFun hA i) j
end Formalism.HermitianLatticesTheory
