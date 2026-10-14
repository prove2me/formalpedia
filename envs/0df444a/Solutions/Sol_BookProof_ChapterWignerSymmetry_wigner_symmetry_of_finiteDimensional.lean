-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:01.714975+00:00
-- url     : https://prove2.me/submissions/f377d175-5bc2-4a42-b97a-8edc129e8af4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_wigner_symmetry
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
variable {b : OrthonormalBasis ι ℂ E} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [Nontrivial F] {T : F → F}
    (hT : IsWignerSymmetry T) :
    (∃ U : F ≃ₗᵢ[ℂ] F, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨
    (∃ U : F → F, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) := by

  have hpos : 0 < Module.finrank ℂ F := Module.finrank_pos
  exact wigner_symmetry (stdOrthonormalBasis ℂ F) ⟨0, hpos⟩ hT
