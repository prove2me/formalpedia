-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:09.180822+00:00
-- url     : https://prove2.me/submissions/b7684bd9-d652-4d67-80d5-3baa647cb73d

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
theorem _root_.solution {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (i : Fin a) : ext1 P i.succ 0 = 0 := rfl
end Formalism.CyclotomicNorms.residueMatrixData
