-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_row_upG_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:32.008189+00:00
-- url     : https://prove2.me/submissions/014b7b90-b085-4861-8949-d950f376b7df

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_linS_rowM_self
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
    (F : MvPowerSeries (I g) C) :
    subst (linS (rowM g e v')) (upG g F) =
      rename (Function.Embedding.inl : ι ↪ ι ⊕ ι') (subst (linS e) F) := by
  unfold upG
  rw [subst_linS_subst _ (fun s => by simp), rename_subst_linS]
  congr 1
  funext x
  rw [subst_linS_X, linS_rowM_self]
end Formalism.L2.FormalSeriesBounds
