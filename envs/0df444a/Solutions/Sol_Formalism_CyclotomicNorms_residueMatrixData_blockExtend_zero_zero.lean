-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:06.389919+00:00
-- url     : https://prove2.me/submissions/1779e1e4-dec4-4cc0-9d83-d4c4f8c87b89

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {R : Type*} [CommRing R]
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : ext1 P 0 0 = 1 := rfl
end Formalism.CyclotomicNorms.residueMatrixData
