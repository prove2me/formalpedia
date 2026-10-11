-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:28.523062+00:00
-- url     : https://prove2.me/submissions/7362dbb5-7312-4250-bc7d-726e504961b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_diagOp_add_one_surjective
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_eq_diagOp
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiWeight_ge_one
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterAbelianDiagonalCountable
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
theorem solution (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (f : FermiFock n) :
    ∃ x : fullDom n, onFull (smFermiN om c0) x + (x : FermiFock n) = f := by

  obtain ⟨ψ, hψ⟩ := diagOp_add_one_surjective
    (fun S => smFermiWeight_ge_one hom hc0 (om := om) (c0 := c0) S) f
  refine ⟨⟨ψ, Submodule.mem_top⟩, ?_⟩
  rw [onFull_apply, smFermiN_eq_diagOp]
  exact hψ
