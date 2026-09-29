-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.essentiallySelfAdjointOn_of_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:54:57.101996+00:00
-- url     : https://prove2.me/submissions/f84ea320-b4ab-4f8b-8e48-b577e1e928bc

-- Generated from ChapterQgHermiteOscillatorEsa.lean — solution of BookProof.QgHermiteOscillator.essentiallySelfAdjointOn_of_eigenbasis
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Theorems.Thm_BookProof_QgHermiteOscillator_deficiencyTrivialAt_of_eigenbasis
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
    (heig : ∀ i, T ⟨b i, hmem i⟩ = ((lam i : ℝ) : ℂ) • (b i : F)) :
    EssentiallySelfAdjointOn D T :=
  ⟨deficiencyTrivialAt_of_eigenbasis T b lam hmem heig (by simp),
      deficiencyTrivialAt_of_eigenbasis T b lam hmem heig (by simp)⟩
