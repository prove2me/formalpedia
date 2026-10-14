-- Prove2me | solution 2 for BookProof.SmDiracYukawa.sm_fermi_N_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T12:11:03.460319+00:00
-- url     : https://prove2.me/submissions/fb6e6780-e3fd-4472-a0c9-5475c5a47819

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.sm_fermi_N_ge_one
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

theorem solution(hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    ‖(x : FermiFock n)‖ ^ 2 ≤ quadForm (onFull (smFermiN om c0)) x := by
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
  have h111 : ∀ (d : Finset (Fin n) → ℝ) (ψ : FermiFock n), (inner ℂ ψ (BookProof.SmDiracYukawa.diagOp d ψ) : ℂ).re = ∑ S, d S * ‖ψ S‖ ^ 2 := by
    intro d ψ
    simp only [BookProof.SmDiracYukawa.diagOp, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro S _
    simp [RCLike.inner_apply, Complex.sq_norm, Complex.normSq_apply] <;> ring
  unfold quadForm onFull
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [hN, h111]
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro S _
  have h0 := Finset.sum_nonneg (fun i (_ : i ∈ S) => hom i)
  have h1 := mul_nonneg (by linarith : (0:ℝ) ≤ ∑ i ∈ S, om i + c0 - 1) (sq_nonneg ‖(x : FermiFock n) S‖)
  nlinarith [h1]
