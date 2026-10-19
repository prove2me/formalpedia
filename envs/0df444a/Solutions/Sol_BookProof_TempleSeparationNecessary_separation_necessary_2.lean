-- Prove2me | solution 2 for BookProof.TempleSeparationNecessary.separation_necessary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:30:42.169217+00:00
-- url     : https://prove2.me/submissions/126868f6-b55a-4134-ac81-57c0518eb061

import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterRitzCertificate
import Theorems.Thm_BookProof_TempleSeparationNecessary_norm_trial
import Theorems.Thm_BookProof_TempleSeparationNecessary_resid_witness
import Theorems.Thm_BookProof_TempleSeparationNecessary_bddBelow_spectrum
import Theorems.Thm_BookProof_TempleSeparationNecessary_rayleigh_witness
import Theorems.Thm_BookProof_TempleSeparationNecessary_neg_mem_spectrum_witness
-- Generated from ChapterTempleSeparationNecessary.lean — theorem BookProof.TempleSeparationNecessary.separation_necessary
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
open BookProof.RitzCertificate
open BookProof.TempleSeparationNecessary


noncomputable section


open BookProof.RitzCertificate
theorem h44_isSA_witness (M : ℝ) (x : BookProof.TempleSeparationNecessary.E2) :
    IsSelfAdjoint (BookProof.TempleSeparationNecessary.witness M x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [BookProof.TempleSeparationNecessary.witness, BookProof.TempleSeparationNecessary.proj,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, inner_conj_symm, Complex.conj_ofReal]
  ring

theorem solution (M : ℝ) :
    ∃ (A : BookProof.TempleSeparationNecessary.E2 →L[ℂ] BookProof.TempleSeparationNecessary.E2) (x : BookProof.TempleSeparationNecessary.E2), IsSelfAdjoint A ∧ ‖x‖ = 1 ∧
      rayleigh A x = 0 ∧ resid A x = 0 ∧ sInf (spectrum ℝ A) ≤ -M := by
  exact ⟨BookProof.TempleSeparationNecessary.witness M BookProof.TempleSeparationNecessary.trial,
    BookProof.TempleSeparationNecessary.trial, h44_isSA_witness M _,
    BookProof.TempleSeparationNecessary.norm_trial,
    BookProof.TempleSeparationNecessary.rayleigh_witness M,
    BookProof.TempleSeparationNecessary.resid_witness M,
    csInf_le (BookProof.TempleSeparationNecessary.bddBelow_spectrum _)
      (BookProof.TempleSeparationNecessary.neg_mem_spectrum_witness M)⟩

