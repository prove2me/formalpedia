-- Prove2me | solution 1 for BookProof.HermiteBand.degree_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:05:03.285538+00:00
-- url     : https://prove2.me/submissions/4ac60579-852a-41b6-8d34-85ed7d6cd59c

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.degree_sub_single
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {α : Fin d →₀ ℕ} {i : Fin d} (h : 1 ≤ α i) :
    (α - Finsupp.single i 1).degree + 1 = α.degree := by

  have hb : α = (α - Finsupp.single i 1) + Finsupp.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  conv_rhs => rw [hb]
  simp
