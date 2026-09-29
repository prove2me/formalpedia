-- Prove2me | solution 1 for BookProof.HermiteProductBasis.hermiteMvNorm_add_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:14.203975+00:00
-- url     : https://prove2.me/submissions/c1ba953b-4982-4a23-afb1-18bb3364095c

-- Generated from ChapterHermiteProductBasis.lean — solution of BookProof.HermiteProductBasis.hermiteMvNorm_add_single
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_HermiteProductBasis_hermiteNorm_succ
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteProductBasis








open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + Finsupp.single i 1) = hermiteMvNorm a * Real.sqrt ((a i : ℝ) + 1) := by

  classical
  have hsplit : ∀ b : Fin d →₀ ℕ, hermiteMvNorm b
      = hermiteNorm (b i) * ∏ j ∈ Finset.univ.erase i, hermiteNorm (b j) := by
    intro b
    rw [hermiteMvNorm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, hermiteNorm ((a + Finsupp.single i 1 : Fin d →₀ ℕ) j)
      = ∏ j ∈ Finset.univ.erase i, hermiteNorm (a j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [show (a + Finsupp.single i 1 : Fin d →₀ ℕ) j = a j by
        simp [Finset.ne_of_mem_erase hj]]
  have hai : (a + Finsupp.single i 1 : Fin d →₀ ℕ) i = a i + 1 := by simp
  rw [hsplit (a + Finsupp.single i 1), hrest, hai, hermiteNorm_succ, hsplit a]
  ring
