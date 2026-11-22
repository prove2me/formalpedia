-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:01.047851+00:00
-- url     : https://prove2.me/submissions/fb006f28-8092-44cc-bbcf-0eef18affb59

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le

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
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (p : Ideal R) [p.IsPrime] (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := Ideal.mem_primeCompl_iff.mp (locBasic_hcompl_le (K := K) p hs)
end Formalism.HermitianLatticesTheory
