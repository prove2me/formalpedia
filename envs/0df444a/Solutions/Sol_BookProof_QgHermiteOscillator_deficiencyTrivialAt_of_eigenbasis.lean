-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.deficiencyTrivialAt_of_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:12.831351+00:00
-- url     : https://prove2.me/submissions/8ea25133-997a-4fa6-9fe6-dc840da39631

-- Generated from ChapterQgHermiteOscillatorEsa.lean — solution of BookProof.QgHermiteOscillator.deficiencyTrivialAt_of_eigenbasis
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Theorems.Thm_BookProof_QgHermiteOscillator_eq_zero_of_inner_basis_eq_zero
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.QgHermiteOscillator












open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ι : Type*} {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (T : D →ₗ[ℂ] F) (b : HilbertBasis ι ℂ F)
    (lam : ι → ℝ) (hmem : ∀ i, (b i : F) ∈ D)
    (heig : ∀ i, T ⟨b i, hmem i⟩ = ((lam i : ℝ) : ℂ) • (b i : F))
    {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt D T z := by

  intro w hw
  refine eq_zero_of_inner_basis_eq_zero b fun i => ?_
  have key := hw ⟨b i, hmem i⟩
  rw [heig i, inner_smul_left] at key
  have hconj : (starRingEnd ℂ) ((lam i : ℝ) : ℂ) = ((lam i : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hconj] at key
  have hne : ((lam i : ℝ) : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    have := congrArg Complex.im h
    simpa [sub_eq_zero] using this.symm
  have : (((lam i : ℝ) : ℂ) - z) * (inner ℂ (b i) w : ℂ) = 0 := by
    rw [sub_mul]
    simpa using sub_eq_zero.mpr key
  exact (mul_eq_zero.mp this).resolve_left hne
