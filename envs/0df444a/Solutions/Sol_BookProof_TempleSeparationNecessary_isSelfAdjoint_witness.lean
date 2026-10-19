-- Prove2me | solution 1 for BookProof.TempleSeparationNecessary.isSelfAdjoint_witness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:30:29.911063+00:00
-- url     : https://prove2.me/submissions/6023b560-7078-462d-b4a3-657eaf427769

import Definitions.Def_ChapterRitzCertificate
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Definitions.Def_ChapterNavierStokesFarisLavineLift
-- Generated from ChapterTempleSeparationNecessary.lean — theorem BookProof.TempleSeparationNecessary.isSelfAdjoint_witness
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
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

theorem solution (M : ℝ) (x : BookProof.TempleSeparationNecessary.E2) : IsSelfAdjoint (witness M x) := by
  exact h44_isSA_witness M x

