-- Prove2me | solution 2 for BookProof.SmDiracYukawa.smFermiN_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T12:20:52.912844+00:00
-- url     : https://prove2.me/submissions/abf49b76-c650-4a89-a274-758dd5bccf95

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiN_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}
open BookProof.SmDiracYukawa

theorem solution(om : Fin n → ℝ) (c0 : ℝ) :
    SymmetricOn (fullDom n) (onFull (smFermiN om c0)) := by
  have h101 : ∀ (i : Fin n) (φ : FermiFock n) (T : Finset (Fin n)), (BookProof.SmCar.creat i (BookProof.SmCar.annih i φ)) T = if i ∈ T then φ T else 0 := by
    intro i φ T
    by_cases h : i ∈ T <;> simp [BookProof.SmCar.creat, BookProof.SmCar.annih, h, Finset.insert_erase, jwSign, ← mul_assoc, ← mul_pow]
  have h104 : ∀ (ψ : FermiFock n) (S : Finset (Fin n)), (fermiEnergy om ψ) S = ((∑ i ∈ S, om i : ℝ) : ℂ) * ψ S := by
    intro ψ S
    unfold fermiEnergy fermiBilin
    simp [LinearMap.sum_apply, Matrix.diagonal_apply, ite_smul, h101, mul_ite, Finset.sum_ite_mem, Finset.sum_mul]
  have hN : ∀ ψ : FermiFock n, smFermiN om c0 ψ = BookProof.SmDiracYukawa.diagOp (fun S => ∑ i ∈ S, om i + c0) ψ := by
    intro ψ
    ext S
    simp [smFermiN, h104, BookProof.SmDiracYukawa.diagOp]
    ring
  have h103 : ∀ (d : Finset (Fin n) → ℝ) (ψ φ : FermiFock n), (inner ℂ (BookProof.SmDiracYukawa.diagOp d ψ) φ : ℂ) = inner ℂ ψ (BookProof.SmDiracYukawa.diagOp d φ) := by
    intro d ψ φ
    simp only [BookProof.SmDiracYukawa.diagOp, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro S _
    simp [RCLike.inner_apply] <;> ring
  intro x y
  simp only [onFull, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [hN, hN, h103]
