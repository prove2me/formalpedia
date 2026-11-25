-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.lift_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:22.744423+00:00
-- url     : https://prove2.me/submissions/4a7c345e-be8a-4769-8979-3eab478f5e71

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Lemmata_MiscLemmasH_Imports
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Theorems.Thm_Bl_SecondBlockLemmaI_goal1


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
theorem _root_.solution [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  first | exact Bl.SecondBlockLemmaI.goal1 .. | (apply Bl.SecondBlockLemmaI.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaI.goal1 <;> assumption)
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
