-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.iwasawa_decomposition_unitary_group
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:10.562828+00:00
-- url     : https://prove2.me/submissions/8760f0c4-fb25-4d13-9c7a-c8d99612bb04

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dec_Jm
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
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : IwaAll := by
  intro n ε
  obtain ⟨U, hU, h⟩ := CholeskyDecomposition.dec_Jm ε
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨k, hk, s, hkJ, hsJ, rfl, htri⟩ := h g hg
  refine ⟨k, ⟨hk, ?_⟩, s, hsJ, rfl, htri⟩
  have hk1 : k * k.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hk
  calc k * Jm ε = k * (k.conjTranspose * Jm ε * k) := by rw [hkJ]
    _ = k * k.conjTranspose * Jm ε * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * k := by rw [hk1, Matrix.one_mul]
end CompanionTheory.D.gk.admitted
