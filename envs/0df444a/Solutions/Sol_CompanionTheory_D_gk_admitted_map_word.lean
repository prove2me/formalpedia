-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.map_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:54.862739+00:00
-- url     : https://prove2.me/submissions/ad19246c-e15e-481c-9c5a-668441e99b22

import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
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
theorem _root_.solution {R' : Type*} [Ring R'] (f : R →+* R') (E : R) (l : List R) :
    f (word E l) = word (f E) (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
end CompanionTheory.D.gk.admitted
