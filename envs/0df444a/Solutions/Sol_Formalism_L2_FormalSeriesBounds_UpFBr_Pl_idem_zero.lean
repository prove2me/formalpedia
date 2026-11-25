-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.idem_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:22.006916+00:00
-- url     : https://prove2.me/submissions/153ed450-2a97-4599-acb7-b8040e316736

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Lemmata_MiscLemmasH_Imports
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {A : Type} [CommRing A] (I : Ideal A)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution [IsHausdorff I A] {f : A} (h : f * f = f) (hf : f ∈ I) : f = 0 := by
  refine IsHausdorff.haus (I := I) ‹_› f fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  rcases n with _ | n
  · simp
  · have he : IsIdempotentElem f := h
    rw [← he.pow_succ_eq n]
    exact Ideal.pow_mem_pow hf _
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
