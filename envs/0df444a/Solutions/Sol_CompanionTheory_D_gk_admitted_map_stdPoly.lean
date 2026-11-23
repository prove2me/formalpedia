-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.map_stdPoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:01.858253+00:00
-- url     : https://prove2.me/submissions/e74190d4-04c2-4f2f-9f56-0f2e993ecf3d

import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_map_word
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons

set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {R : Type*} [Ring R]
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {R' : Type*} [Ring R'] (f : R →+* R') (E : R) {M : ℕ} (a : Fin M → R) :
    f (stdPoly E a) = stdPoly (f E) fun i => f (a i) := by
  simp [stdPoly, map_word, List.map_ofFn, Function.comp_def]
end CompanionTheory.D.gk.admitted
