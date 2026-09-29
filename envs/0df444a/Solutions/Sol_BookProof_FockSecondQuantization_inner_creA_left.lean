-- Prove2me | solution 1 for BookProof.FockSecondQuantization.inner_creA_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:07.326984+00:00
-- url     : https://prove2.me/submissions/b79b8451-2f13-415d-9333-4d4dfd366c49

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.inner_creA_left
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_up_self
import Theorems.Thm_BookProof_FockSecondQuantization_dn_up
import Theorems.Thm_BookProof_FockSecondQuantization_up_injective
import Theorems.Thm_BookProof_FockSecondQuantization_annA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_support_creA
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp_of_subset
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (j : ℕ) (u v : FockAlg) :
    (inner ℂ (toLp (creA j u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (annA j v)) := by

  rw [inner_toLp_of_subset (support_creA j u) v, inner_toLp u (annA j v),
    Finset.sum_image (fun x _ y _ h => up_injective j h)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [creA_apply, up_self, dn_up, annA_apply]
  have hcast : ((β j + 1 : ℕ) : ℝ) = ((β j : ℝ) + 1) := by push_cast; ring
  rw [hcast, map_mul, Complex.conj_ofReal]
  ring
