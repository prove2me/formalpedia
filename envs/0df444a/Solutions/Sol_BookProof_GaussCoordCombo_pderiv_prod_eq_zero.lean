-- Prove2me | solution 1 for BookProof.GaussCoordCombo.pderiv_prod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:44:26.94387+00:00
-- url     : https://prove2.me/submissions/a243dcc3-a21c-406e-b60e-2acdae02616e

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.pderiv_prod_eq_zero
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ}
    {i : Fin d} (h : ∀ j ∈ S, pderiv i (W j) = 0) : pderiv i (∏ j ∈ S, W j) = 0 := by

  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Derivation.leibniz,
        h a (Finset.mem_insert_self a S),
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
      simp
