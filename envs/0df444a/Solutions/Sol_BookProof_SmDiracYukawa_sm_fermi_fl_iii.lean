-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_fl_iii
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:08:44.201194+00:00
-- url     : https://prove2.me/submissions/283c1ad5-a54b-4efe-b725-acb6f2abd277

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_fl_iii
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_norm_le
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiBound_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiOm_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_norm_le
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_norm_ge
import Theorems.Thm_BookProof_SmDiracYukawa_norm_dcommOp_le
import Definitions.Def_ChapterFarisLavine
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
    |(inner ℂ (x : FermiFock n)
        (dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)) : ℂ).re|
      ≤ (4 * smFermiBound hD M z * smFermiOm om c0 ^ 2)
        * ‖smFermiN om c0 (x : FermiFock n)‖ ^ 2 := by

  have hb := smFermiBound_nonneg hD M z
  have hOm := smFermiOm_nonneg (om := om) (c0 := c0) hom hc0
  have hdc := norm_dcommOp_le (H := smFermiHam hD M z) (N := smFermiN om c0)
    (K := smFermiBound hD M z) (Om := smFermiOm om c0)
    (fun ψ => smFermiHam_norm_le hD M z ψ) (fun ψ => sm_fermi_N_norm_le hom hc0 ψ) hb hOm
    (x : FermiFock n)
  have hCS : |(inner ℂ (x : FermiFock n)
      (dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)) : ℂ).re|
      ≤ ‖(x : FermiFock n)‖
        * ‖dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)‖ :=
    le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
  have hxN := sm_fermi_N_norm_ge hom hc0 (x : FermiFock n)
  have hx : (0:ℝ) ≤ ‖(x : FermiFock n)‖ := norm_nonneg _
  have hcoef : (0:ℝ) ≤ 4 * smFermiBound hD M z * smFermiOm om c0 ^ 2 := by positivity
  calc |(inner ℂ (x : FermiFock n)
        (dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)) : ℂ).re|
      ≤ ‖(x : FermiFock n)‖
          * ‖dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)‖ := hCS
    _ ≤ ‖(x : FermiFock n)‖
          * (4 * smFermiBound hD M z * smFermiOm om c0 ^ 2 * ‖(x : FermiFock n)‖) :=
        mul_le_mul_of_nonneg_left hdc hx
    _ = (4 * smFermiBound hD M z * smFermiOm om c0 ^ 2) * ‖(x : FermiFock n)‖ ^ 2 := by ring
    _ ≤ (4 * smFermiBound hD M z * smFermiOm om c0 ^ 2)
          * ‖smFermiN om c0 (x : FermiFock n)‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        nlinarith [hxN, norm_nonneg (smFermiN om c0 (x : FermiFock n))]
