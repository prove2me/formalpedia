-- Prove2me | solution 1 for Formalism.L2.DIV.restrFrameSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:01.885471+00:00
-- url     : https://prove2.me/submissions/a54e90af-f116-4eaf-90bb-432e728e6027

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_map_inj
import Theorems.Thm_Formalism_L2_DIV_majAt_eq
import Theorems.Thm_Formalism_L2_DIV_emb_mulVec
import Theorems.Thm_Formalism_L2_DIV_frameOfSpec
import Theorems.Thm_Formalism_L2_DIV_quotRestrPosDef

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
theorem _root_.solution : RestrFrameSpec := by
  intro K _ _ _ n d H h2 E hE v
  have hs := frameOfSpec d _ ((quotRestrPosDef n d _ (h2 v)).2 _ (map_inj v.embedding E hE))
  refine ⟨hs.1, hs.2, fun x y => ?_⟩
  have hm1 : metOf (restrFrame E H v) = restrMetC (E.map v.embedding) (H.map v.embedding) := hs.2
  have hm2 : metOf (stdFrame H v) = H.map v.embedding := (frameOfSpec n _ (h2 v)).2
  rw [majAt_eq, majAt_eq, hm1, hm2, emb_mulVec, emb_mulVec, restrMetC, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
end Formalism.L2.DIV
