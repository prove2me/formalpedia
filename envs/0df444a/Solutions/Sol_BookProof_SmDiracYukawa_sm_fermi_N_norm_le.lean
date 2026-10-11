-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_N_norm_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:07:04.071086+00:00
-- url     : https://prove2.me/submissions/48979de6-2934-47e2-b0d1-812c77a9fb76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_N_norm_le
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_diagOp_norm_le
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_eq_diagOp
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiWeight_le
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiOm_nonneg
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
    ‖smFermiN om c0 ψ‖ ≤ smFermiOm om c0 * ‖ψ‖ := by

  rw [smFermiN_eq_diagOp]
  exact diagOp_norm_le (smFermiOm_nonneg hom hc0) (fun S => smFermiWeight_le hom hc0 S) ψ
