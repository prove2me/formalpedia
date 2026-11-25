-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_row_upG_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:05:05.700828+00:00
-- url     : https://prove2.me/submissions/87cb43c7-a4f2-4430-860f-b51467bf4d15

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_linS_rowM_other
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rename_subst_linS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (F : MvPowerSeries (I (1 - g)) C) :
    subst (linS (rowM g e v')) (upG (1 - g) F) =
      rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (subst (linS v') F) := by
  unfold upG
  rw [subst_linS_subst _ (fun s => by simp), rename_subst_linS]
  congr 1
  funext x
  rw [subst_linS_X, linS_rowM_other]
end Formalism.L2.FormalSeriesBounds
