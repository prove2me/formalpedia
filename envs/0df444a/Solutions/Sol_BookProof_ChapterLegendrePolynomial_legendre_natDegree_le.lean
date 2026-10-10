-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.legendre_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:31:43.50713+00:00
-- url     : https://prove2.me/submissions/a440c026-3491-486b-929a-0654414b3e7c

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.legendre_natDegree_le
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendreAux_natDegree_le
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) : (legendre l).natDegree ≤ l := le_trans (natDegree_C_mul_le _ _) (legendreAux_natDegree_le l)
