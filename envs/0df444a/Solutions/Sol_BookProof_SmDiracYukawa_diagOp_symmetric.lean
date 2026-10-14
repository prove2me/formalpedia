-- Prove2me | solution 1 for BookProof.SmDiracYukawa.diagOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:27:29.021189+00:00
-- url     : https://prove2.me/submissions/676f4eb9-3256-4fd8-aaed-6ba309bae827

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_symmetric
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

theorem solution(d : Finset (Fin n) → ℝ) (ψ φ : FermiFock n) :
    (inner ℂ (diagOp d ψ) φ : ℂ) = inner ℂ ψ (diagOp d φ) := by
  simp only [BookProof.SmDiracYukawa.diagOp, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro S _
  simp [RCLike.inner_apply] <;> ring
