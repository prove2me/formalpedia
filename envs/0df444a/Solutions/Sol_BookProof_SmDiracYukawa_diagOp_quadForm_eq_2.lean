-- Prove2me | solution 2 for BookProof.SmDiracYukawa.diagOp_quadForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:59:21.564159+00:00
-- url     : https://prove2.me/submissions/84b65233-e7f3-4534-a6dc-db30fceadc14

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_quadForm_eq
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section
open BookProof.SmDiracYukawa

theorem solution(d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    (inner ℂ ψ (diagOp d ψ) : ℂ).re = ∑ S : Finset (Fin n), d S * ‖ψ S‖ ^ 2 := by
  simp only [BookProof.SmDiracYukawa.diagOp, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro S _
  simp [RCLike.inner_apply, Complex.sq_norm, Complex.normSq_apply] <;> ring
