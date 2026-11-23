-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.finrank_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:42.494148+00:00
-- url     : https://prove2.me/submissions/562bdb0a-ade1-45aa-80c9-a2c1f7e6b64b

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
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (W N : Submodule (TruncK K' n) (Fin a → TruncK K' n)) (h : N ≤ W) :
    Module.finrank K' (W ⧸ N.comap W.subtype) + Module.finrank K' N = Module.finrank K' W := by
  have e1 := (Submodule.Quotient.restrictScalarsEquiv K' (N.comap W.subtype)).finrank_eq
  have e2 := ((Submodule.comapSubtypeEquivOfLe h).restrictScalars K').finrank_eq
  rw [← e1, ← e2]
  exact Submodule.finrank_quotient_add_finrank ((N.comap W.subtype).restrictScalars K')
end Formalism.CyclotomicNorms.residueMatrixData
