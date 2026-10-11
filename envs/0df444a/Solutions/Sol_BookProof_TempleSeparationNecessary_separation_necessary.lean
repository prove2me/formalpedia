-- Prove2me | solution 1 for BookProof.TempleSeparationNecessary.separation_necessary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:10.260367+00:00
-- url     : https://prove2.me/submissions/a74c4c0f-5fd1-42c3-935d-24b0050b2122
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterTempleSeparationNecessary.lean — solution of BookProof.TempleSeparationNecessary.separation_necessary
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Theorems.Thm_BookProof_TempleSeparationNecessary_isSelfAdjoint_witness
import Theorems.Thm_BookProof_TempleSeparationNecessary_norm_trial
import Theorems.Thm_BookProof_TempleSeparationNecessary_rayleigh_witness
import Theorems.Thm_BookProof_TempleSeparationNecessary_resid_witness
import Theorems.Thm_BookProof_TempleSeparationNecessary_neg_mem_spectrum_witness
import Theorems.Thm_BookProof_TempleSeparationNecessary_bddBelow_spectrum
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterRitzCertificate
open BookProof.TempleSeparationNecessary



noncomputable section


open BookProof.RitzCertificate

set_option maxHeartbeats 1000000 in
theorem solution (M : ℝ) :
    ∃ (A : E2 →L[ℂ] E2) (x : E2), IsSelfAdjoint A ∧ ‖x‖ = 1 ∧
      rayleigh A x = 0 ∧ resid A x = 0 ∧ sInf (spectrum ℝ A) ≤ -M :=
  ⟨witness M trial, trial, isSelfAdjoint_witness M trial, norm_trial,
      rayleigh_witness M, resid_witness M,
      csInf_le (bddBelow_spectrum _) (neg_mem_spectrum_witness M)⟩
