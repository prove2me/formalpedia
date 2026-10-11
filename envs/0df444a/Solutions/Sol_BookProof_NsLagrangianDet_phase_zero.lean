-- Prove2me | solution 1 for BookProof.NsLagrangianDet.phase_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:56:43.896978+00:00
-- url     : https://prove2.me/submissions/90512039-1fdc-493b-8cb6-88ebc6cd89ed

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.phase_zero
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]
open BookProof.NsLagrangianDet

theorem solution(a : Fin 3 → ℝ) : phase 0 a = 1 := by
  simp [phase]
