-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.constantCoeff_upG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:42.48327+00:00
-- url     : https://prove2.me/submissions/061c8b1e-cb4b-491c-ab82-9a50d18ea353

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_one_iff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : constantCoeff F = 0) :
    constantCoeff (upG g F : MvPowerSeries (WV I) C) = 0 := by
  unfold upG
  exact (ordGE_one_iff _).1 (ordGE_subst (fun x => Formalism.BaseCaseIdentities.OrdGE.X _) ((ordGE_one_iff _).2 hF))
end Formalism.L2.FormalSeriesBounds
