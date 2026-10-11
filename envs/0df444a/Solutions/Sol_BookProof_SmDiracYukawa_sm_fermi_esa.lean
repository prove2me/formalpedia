-- Prove2me | solution 1 for BookProof.SmDiracYukawa.sm_fermi_esa
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:08:58.456648+00:00
-- url     : https://prove2.me/submissions/e88e94e9-2560-491d-9cf5-436aae6058de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.sm_fermi_esa
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_norm_le
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiBound_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiOm_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_symmetricOn
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_symmetricOn
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_nonneg
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_add_one_surjective
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_fl_ii
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_core_of_farisLavine
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
theorem solution (hh : hD.conjTranspose = hD) (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) :
    EssentiallySelfAdjointOn (fullDom n)
      ((onFull (smFermiHam hD M z)).comp (Submodule.inclusion (le_refl (fullDom n)))) := by

  have hb := smFermiBound_nonneg hD M z
  have hOm := smFermiOm_nonneg (om := om) (c0 := c0) hom hc0
  refine essentiallySelfAdjointOn_core_of_farisLavine (le_refl (fullDom n))
    (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0))
    0 (smFermiBound hD M z ^ 2) (2 * smFermiBound hD M z * smFermiOm om c0)
    (smFermiHam_symmetricOn hh) (smFermiN_symmetricOn om c0) (by positivity)
    (sm_fermi_N_nonneg hom hc0) (sm_fermi_N_add_one_surjective hom hc0)
    (fun x => sm_fermi_fl_ii hom hc0 x) (fun x => ?_) (fun x ε hε => ⟨x, trivial, ?_, ?_⟩)
  · have hK : ‖smFermiHam hD M z (x : FermiFock n)‖
        ≤ smFermiBound hD M z * ‖(x : FermiFock n)‖ := smFermiHam_norm_le hD M z _
    have hx : (0:ℝ) ≤ ‖(x : FermiFock n)‖ := norm_nonneg _
    have hsq : ‖onFull (smFermiHam hD M z) x‖ ^ 2
        ≤ (smFermiBound hD M z * ‖(x : FermiFock n)‖) ^ 2 := by
      rw [onFull_apply]
      have h0 : (0:ℝ) ≤ ‖smFermiHam hD M z (x : FermiFock n)‖ := norm_nonneg _
      nlinarith [mul_nonneg hb hx]
    have hexp : (smFermiBound hD M z * ‖(x : FermiFock n)‖) ^ 2
        = 0 * ‖onFull (smFermiN om c0) x‖ ^ 2
          + smFermiBound hD M z ^ 2 * ‖(x : FermiFock n)‖ ^ 2 := by ring
    linarith [hsq, hexp.le, hexp.ge]
  · simpa using hε
  · simpa using hε
