-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.conjTranspose_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:15.42481+00:00
-- url     : https://prove2.me/submissions/22697c5b-ee00-413a-805e-13f929416d64

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank
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
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : mᴴ ∈ UJset ε := by
  have h1 := mul_eq_one_comm.1 (coeMatrix_left_inv ε m hm)
  show mᴴᴴ * Jm ε * mᴴ = Jm ε
  rw [Matrix.conjTranspose_conjTranspose]
  calc m * Jm ε * mᴴ = m * (Jm ε * mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]
end CompanionTheory.D.gk.admitted
