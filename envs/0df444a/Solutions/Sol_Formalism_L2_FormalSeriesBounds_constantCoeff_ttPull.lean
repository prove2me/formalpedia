-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.constantCoeff_ttPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:28.154471+00:00
-- url     : https://prove2.me/submissions/8acc05ef-4adf-4c2b-9cf7-e1e84adfadf5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_one_iff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst_linS

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
theorem _root_.solution (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, constantCoeff (t g c) = 0) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (s : I g ⊕ I (1 - g)) : constantCoeff (ttPull t g e v' s) = 0 := by
  rcases s with c | c
  · show constantCoeff (rename _ (subst (linS e) (t g c))) = 0
    rw [constantCoeff_rename]
    exact (ordGE_one_iff _).1 (ordGE_subst_linS e ((ordGE_one_iff _).2 (ht0 g c)))
  · show constantCoeff (rename _ (subst (linS v') (t (1 - g) c))) = 0
    rw [constantCoeff_rename]
    exact (ordGE_one_iff _).1 (ordGE_subst_linS v' ((ordGE_one_iff _).2 (ht0 (1 - g) c)))
end Formalism.L2.FormalSeriesBounds
