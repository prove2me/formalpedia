-- Prove2me | solution 1 for BookProof.ChapterA3.lemma48_bridge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:37:50.848103+00:00
-- url     : https://prove2.me/submissions/e707c63a-3e54-455e-81b7-081ab788e451

-- Generated from ChapterA3i.lean — solution of BookProof.ChapterA3.lemma48_bridge
import Mathlib
import Definitions.Def_ChapterA3i
import Theorems.Thm_BookProof_ChapterA3_spinorInv_conj_mgamma
import Theorems.Thm_BookProof_ChapterA3_spinor_inv_eq
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) (μ : Fin 4) :
    (Spinor T)⁻¹ * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν μ • mgamma ν := by

  rw [spinor_inv_eq T hdet]
  exact spinorInv_conj_mgamma T μ
