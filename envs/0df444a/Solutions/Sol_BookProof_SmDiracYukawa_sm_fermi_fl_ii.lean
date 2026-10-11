-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_fl_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:08:01.183309+00:00
-- url     : https://prove2.me/submissions/276215b4-819a-48a2-be1e-8b308f84e3b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_fl_ii
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_norm_le
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiBound_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiOm_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_ge_one
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_norm_le
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}
variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    |commForm (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0)) x|
      ≤ (2 * smFermiBound hD M z * smFermiOm om c0)
        * quadForm (onFull (smFermiN om c0)) x := by

  have hK : ‖smFermiHam hD M z (x : FermiFock n)‖
      ≤ smFermiBound hD M z * ‖(x : FermiFock n)‖ := smFermiHam_norm_le hD M z _
  have hNb := sm_fermi_N_norm_le hom hc0 (x : FermiFock n)
  have hb := smFermiBound_nonneg hD M z
  have hOm := smFermiOm_nonneg (om := om) (c0 := c0) hom hc0
  have hx : (0:ℝ) ≤ ‖(x : FermiFock n)‖ := norm_nonneg _
  have hcomm : |commForm (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0)) x|
      ≤ 2 * (‖smFermiHam hD M z (x : FermiFock n)‖ * ‖smFermiN om c0 (x : FermiFock n)‖) := by
    have him : |(inner ℂ (onFull (smFermiHam hD M z) x) (onFull (smFermiN om c0) x) : ℂ).im|
        ≤ ‖smFermiHam hD M z (x : FermiFock n)‖ * ‖smFermiN om c0 (x : FermiFock n)‖ :=
      le_trans (Complex.abs_im_le_norm _) (norm_inner_le_norm _ _)
    have habs : |(-2 : ℝ) * (inner ℂ (onFull (smFermiHam hD M z) x)
          (onFull (smFermiN om c0) x) : ℂ).im|
        = 2 * |(inner ℂ (onFull (smFermiHam hD M z) x)
          (onFull (smFermiN om c0) x) : ℂ).im| := by
      rw [abs_mul]
      norm_num
    rw [commForm_eq, habs]
    linarith
  have hprod : ‖smFermiHam hD M z (x : FermiFock n)‖ * ‖smFermiN om c0 (x : FermiFock n)‖
      ≤ (smFermiBound hD M z * smFermiOm om c0) * ‖(x : FermiFock n)‖ ^ 2 := by
    have h1 : (0:ℝ) ≤ ‖smFermiN om c0 (x : FermiFock n)‖ := norm_nonneg _
    nlinarith [norm_nonneg (smFermiHam hD M z (x : FermiFock n))]
  have hN := sm_fermi_N_ge_one hom hc0 x
  have hcoef : (0:ℝ) ≤ 2 * smFermiBound hD M z * smFermiOm om c0 := by positivity
  calc |commForm (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0)) x|
      ≤ 2 * (‖smFermiHam hD M z (x : FermiFock n)‖
          * ‖smFermiN om c0 (x : FermiFock n)‖) := hcomm
    _ ≤ 2 * ((smFermiBound hD M z * smFermiOm om c0) * ‖(x : FermiFock n)‖ ^ 2) := by
        linarith
    _ = (2 * smFermiBound hD M z * smFermiOm om c0) * ‖(x : FermiFock n)‖ ^ 2 := by ring
    _ ≤ (2 * smFermiBound hD M z * smFermiOm om c0)
          * quadForm (onFull (smFermiN om c0)) x := mul_le_mul_of_nonneg_left hN hcoef
