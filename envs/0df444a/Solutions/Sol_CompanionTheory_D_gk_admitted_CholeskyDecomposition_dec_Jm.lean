-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.dec_Jm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:29.229688+00:00
-- url     : https://prove2.me/submissions/5599933d-f08c-402a-b638-e5d6f342e690

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dec_of_monotone
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Dec_of_conj
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
theorem _root_.solution (ε : Fin n → Bool) : Dec (Jm ε) := by
  classical
  let σ := Tuple.sort ε
  have hmono : Monotone (ε ∘ σ) := Tuple.monotone_sort ε
  let V : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id σ
  have hV : ∀ H : Matrix (Fin n) (Fin n) ℂ, V.conjTranspose * H * V = H.submatrix σ σ := by
    intro H
    ext a b
    simp [V, Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  apply Dec.of_conj (V := V)
  · have h1 := hV 1
    rw [Matrix.mul_one] at h1
    rw [h1]
    exact Matrix.submatrix_one_equiv σ
  · rw [hV]
    have h2 : (Jm ε).submatrix σ σ = Jm (ε ∘ σ) := by
      unfold Jm
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [h2]
    exact dec_of_monotone hmono
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
