-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY2_nsSymbol2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:22:58.552157+00:00
-- url     : https://prove2.me/submissions/747aad4a-fd74-4d45-82c3-550e5de92ab7

import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY2_nsSymbol2
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY
lemma h42_half : (C (2⁻¹:ℂ) : NSAlg) * 2 = 1 := by
  have h : (C (2:ℂ) : NSAlg) = 2 := map_ofNat C 2
  rw [← h, ← map_mul]; norm_num
lemma h42_y (k j : Fin 3) : pderiv (NSVar.y j) (uField2 k) = uDField k j := by
  simp [uField2, uDField, pderiv_X, Pi.single_apply, Fin.sum_univ_three]
  fin_cases j <;> simp <;> linear_combination (X (NSVar.uL k) * X (NSVar.y _)) * h42_half
lemma h42_u (k m : Fin 3) : pderiv (NSVar.u m) (uField2 k) = if k = m then 1 else 0 := by
  simp [uField2, pderiv_X, Pi.single_apply, Fin.sum_univ_three]
lemma h42_uD (k m j : Fin 3) : pderiv (NSVar.uD m j) (uField2 k) = if k = m then X (NSVar.y j) else 0 := by
  simp [uField2, pderiv_X, Pi.single_apply, Fin.sum_univ_three]
  fin_cases j <;> simp

theorem solution (nu : ℂ) (i j : Fin 3) : genY2 j (nsSymbol2 nu i) = 0 := by
  simp [genY2, nsSymbol2, h42_y, h42_u, h42_uD, uDField, pderiv_X, Pi.single_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

