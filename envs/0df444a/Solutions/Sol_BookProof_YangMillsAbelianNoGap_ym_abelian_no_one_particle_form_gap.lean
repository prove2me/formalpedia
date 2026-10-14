-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.ym_abelian_no_one_particle_form_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:01.190138+00:00
-- url     : https://prove2.me/submissions/a4f59715-75d3-4001-9009-644cee19a5e7

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.ym_abelian_no_one_particle_form_gap
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_exists_core_state_small_energy
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ ≃ (Fin 99 →₀ ℕ)) {mu : ℝ} (hmu : 0 < mu) :
    ¬ ∀ x : finiteModeDomain (coreBasis e),
      mu * ‖(x : L2d 99)‖ ^ 2
        ≤ quadForm (ymHamiltonian (coreRepBasis e) (fun _ _ _ => (0 : ℝ))) x := by

  intro hgap
  obtain ⟨x, hx0, hxle⟩ := exists_core_state_small_energy e (ε := mu / 2) (by positivity)
  have hnorm : 0 < ‖(x : L2d 99)‖ ^ 2 := by
    have : (0 : ℝ) < ‖(x : L2d 99)‖ := norm_pos_iff.mpr hx0
    positivity
  have h := hgap x
  nlinarith [h, hxle, hnorm]
