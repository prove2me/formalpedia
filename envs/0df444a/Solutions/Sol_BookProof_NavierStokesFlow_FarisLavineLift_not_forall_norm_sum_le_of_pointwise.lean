-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:29:31.583563+00:00
-- url     : https://prove2.me/submissions/fb317fc0-96f4-4cd1-8090-6b7b06817cd3

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution :
    ∃ (h n : Fin 2 → (E2 →ₗ[ℂ] E2)) (v : E2),
      (∀ (k : Fin 2) (x : E2), ‖h k x‖ ≤ ‖n k x‖) ∧
        ‖(n 0 + n 1) v‖ < ‖(h 0 + h 1) v‖  := by
  refine ⟨hEx, nEx, vEx, ?_, ?_⟩
  · intro k x
    simp [hEx, nEx, norm_smul, EuclideanSpace.norm_single]
  · have hh : (hEx 0 + hEx 1) vEx = (2 : ℂ) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by
      ext i
      fin_cases i <;> norm_num [hEx, vEx]
    have hn : (nEx 0 + nEx 1) vEx = vEx := by
      ext i
      fin_cases i <;> simp [nEx, vEx]
    rw [hh, hn]
    have hv : ‖vEx‖ ^ 2 = 2 := by
      norm_num [EuclideanSpace.norm_sq_eq, vEx, Fin.sum_univ_two]
    simp only [norm_smul, Complex.norm_ofNat, EuclideanSpace.norm_single, norm_one, mul_one]
    nlinarith [norm_nonneg vEx]

#print axioms solution
