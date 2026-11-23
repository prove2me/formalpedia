-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.ht_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:49.206538+00:00
-- url     : https://prove2.me/submissions/64a9b030-e91f-49ea-ab16-bfc7514cc82e

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_ht_ne
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open Matrix PI.UpqRep
open CompanionTheory.D.gk.admitted.CholeskyDecomposition
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {ε : Fin n → Bool} {i : Fin n} : ht ε i = 0 ↔ ε i.rev = ε i := by
  unfold ht
  by_cases h : ε i.rev = ε i
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun e => absurd e (ht_ne h), fun e => absurd e h⟩
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
