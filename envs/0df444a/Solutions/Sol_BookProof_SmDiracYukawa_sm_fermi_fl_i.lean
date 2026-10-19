-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_fl_i
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:07:06.16186+00:00
-- url     : https://prove2.me/submissions/229a8fc3-54c2-4172-9974-ef2172f43f25

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_fl_i
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_norm_le
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiBound_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_ge_one
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine
open BookProof.SmCar

variable {n : ℕ}

noncomputable section

variable {n : ℕ}
variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}


@[simp] private theorem onFull_apply (T : FermiFock n →ₗ[ℂ] FermiFock n) (x : fullDom n) :
    onFull T x = T (x : FermiFock n) := rfl

set_option maxHeartbeats 1000000 in
theorem solution (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    |quadForm (onFull (smFermiHam hD M z)) x|
      ≤ smFermiBound hD M z * quadForm (onFull (smFermiN om c0)) x := by

  have hK := smFermiHam_norm_le hD M z (x : FermiFock n)
  have hCS : |quadForm (onFull (smFermiHam hD M z)) x|
      ≤ ‖smFermiHam hD M z (x : FermiFock n)‖ * ‖(x : FermiFock n)‖ := by
    rw [quadForm]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [onFull_apply]
    exact le_trans (norm_inner_le_norm _ _) (by rw [mul_comm])
  have hN := sm_fermi_N_ge_one hom hc0 x
  have hb := smFermiBound_nonneg hD M z
  have hx : (0:ℝ) ≤ ‖(x : FermiFock n)‖ := norm_nonneg _
  calc |quadForm (onFull (smFermiHam hD M z)) x|
      ≤ ‖smFermiHam hD M z (x : FermiFock n)‖ * ‖(x : FermiFock n)‖ := hCS
    _ ≤ (smFermiBound hD M z * ‖(x : FermiFock n)‖) * ‖(x : FermiFock n)‖ := by
        exact mul_le_mul_of_nonneg_right hK hx
    _ = smFermiBound hD M z * ‖(x : FermiFock n)‖ ^ 2 := by ring
    _ ≤ smFermiBound hD M z * quadForm (onFull (smFermiN om c0)) x :=
        mul_le_mul_of_nonneg_left hN hb
