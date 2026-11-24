-- Prove2me | solution 1 for Formalism.L2.DIV.quotFrameHermAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:57.259809+00:00
-- url     : https://prove2.me/submissions/b063df7a-9302-4127-91c5-62c5bbb6b1a7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_inj_of_left_inv
import Theorems.Thm_Formalism_L2_DIV_quotFrameIsQuot
import Theorems.Thm_Formalism_L2_DIV_restrFrameHermAt
import Theorems.Thm_Formalism_L2_DIV_quotEqRestrAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : QuotFrameHermAt := by
  intro K _ _ _ v0 hv0 n d H hH E Pr hP
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hinj : Function.Injective E.mulVec := inj_of_left_inv hP.1
  refine ⟨fun v => (quotFrameIsQuot K n d H hH Pr hsurj v).1, ?_⟩
  rw [quotEqRestrAt K v0 hv0 n d H (hH v0) E Pr hP]
  exact (restrFrameHermAt K v0 hv0 n d H hH E hinj).2
end Formalism.L2.DIV
