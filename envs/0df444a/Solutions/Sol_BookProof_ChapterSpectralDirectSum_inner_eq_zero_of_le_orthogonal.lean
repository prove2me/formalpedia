-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:08.327982+00:00
-- url     : https://prove2.me/submissions/ed874b53-1977-419b-a74d-73d36181d2a5

-- Generated from ChapterSpectralDirectSum.lean — solution of BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_le_orthogonal
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterSpectralDirectSum



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

set_option maxHeartbeats 1000000 in
theorem solution {M N : Submodule ℂ H} (h : M ≤ Nᗮ) {a b : H}
    (ha : a ∈ M) (hb : b ∈ N) : inner ℂ a b = 0 := by

  have h0 := (Submodule.mem_orthogonal N a).1 (h ha) b hb
  simpa [inner_eq_zero_symm] using h0
