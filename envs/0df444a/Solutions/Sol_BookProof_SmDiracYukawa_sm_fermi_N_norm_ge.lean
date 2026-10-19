-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_N_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:07:05.166201+00:00
-- url     : https://prove2.me/submissions/49a19ebc-5ab6-42c0-afe0-47c02a8323f7

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_N_norm_ge
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_diagOp_norm_ge
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_eq_diagOp
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiWeight_ge_one
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}
variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (ψ : FermiFock n) :
    ‖ψ‖ ≤ ‖smFermiN om c0 ψ‖ := by

  rw [smFermiN_eq_diagOp]
  exact diagOp_norm_ge (fun S => smFermiWeight_ge_one hom hc0 S) ψ
