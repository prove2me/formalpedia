-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.sum_embeddings_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:54.896794+00:00
-- url     : https://prove2.me/submissions/e3630af3-d108-4a5a-a09a-e289fcb86c30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SumEmbeddingsEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (z : E) :
    (((Algebra.trace ℚ E z : ℚ) : ℂ)) = ∑ σ : E →+* ℂ, σ z := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
end Formalism.L2.Pj.DatLin
