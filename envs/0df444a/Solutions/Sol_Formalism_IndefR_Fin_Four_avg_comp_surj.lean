-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.avg_comp_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:11.955603+00:00
-- url     : https://prove2.me/submissions/83a7b453-70da-4d06-82a8-a2b63e6cb5dc

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Bl_SecondBlockLemmaD_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * ∑ a, G (π a) = (Fintype.card B : ℂ)⁻¹ * ∑ b, G b := by
  first | exact Bl.SecondBlockLemmaD.goal1 .. | (apply Bl.SecondBlockLemmaD.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaD.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaD.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaD.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaD.goal1 <;> first | assumption | infer_instance)
end Formalism.IndefR.Fin.Four
