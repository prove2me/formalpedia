-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:07.550061+00:00
-- url     : https://prove2.me/submissions/b957c7f1-5ad2-4c34-a072-d631a8a9a0b0

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
theorem _root_.solution {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (j : Fin a) : ext1 P 0 j.succ = 0 := rfl
end Formalism.CyclotomicNorms.residueMatrixData
