-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_N_ge_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:27.206697+00:00
-- url     : https://prove2.me/submissions/8901f8f1-b805-43ed-95f8-f712ee1d3da6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_N_ge_one
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_diagOp_quadForm_eq
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_eq_diagOp
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiWeight_ge_one
import Theorems.Thm_BookProof_SmCar_normSq_eq_sum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.SmCar

variable {n : ℕ}

noncomputable section

variable {n : ℕ}
variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}


@[simp] private theorem onFull_apply (T : FermiFock n →ₗ[ℂ] FermiFock n) (x : fullDom n) :
    onFull T x = T (x : FermiFock n) := rfl

set_option maxHeartbeats 1000000 in
theorem solution (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    ‖(x : FermiFock n)‖ ^ 2 ≤ quadForm (onFull (smFermiN om c0)) x := by

  rw [quadForm, onFull_apply, smFermiN_eq_diagOp, diagOp_quadForm_eq, normSq_eq_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  have h1 := smFermiWeight_ge_one hom hc0 (om := om) (c0 := c0) S
  nlinarith [norm_nonneg ((x : FermiFock n) S), sq_nonneg ‖(x : FermiFock n) S‖]
