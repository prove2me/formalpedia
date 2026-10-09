-- Prove2me | solution 1 for BookProof.GaussCoordCombo.gaussInt_prod_coordFactor
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:44:51.991404+00:00
-- url     : https://prove2.me/submissions/cfd350d2-7e67-44c7-a1af-c2bd91e1e6d2

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.gaussInt_prod_coordFactor
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Theorems.Thm_BookProof_GaussCoordCombo_pderiv_prod_eq_zero
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ}
    {s : Fin d → ℝ} (hW : ∀ j ∈ S, CoordFactor j (W j) (s j))
    {R : MvPolynomial (Fin d) ℂ} (hR : ∀ j ∈ S, pderiv j R = 0) :
    gaussInt ((∏ j ∈ S, W j) * ((∏ j ∈ S, W j) * R))
      = ((∏ j ∈ S, s j : ℝ) : ℂ) * gaussInt R := by

  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      have hWa := hW a (Finset.mem_insert_self a S)
      have hWS : ∀ j ∈ S, CoordFactor j (W j) (s j) := fun j hj =>
        hW j (Finset.mem_insert_of_mem hj)
      have hRS : ∀ j ∈ S, pderiv j R = 0 := fun j hj => hR j (Finset.mem_insert_of_mem hj)
      set Q : MvPolynomial (Fin d) ℂ := ∏ j ∈ S, W j with hQ
      have hpQ : pderiv a Q = 0 := by
        refine pderiv_prod_eq_zero (fun j hj => ?_)
        exact (hWS j hj).1 a (fun hja => ha (hja ▸ hj))
      have hpR : pderiv a R = 0 := hR a (Finset.mem_insert_self a S)
      have hpQQR : pderiv a (Q * (Q * R)) = 0 := by
        rw [Derivation.leibniz, hpQ, Derivation.leibniz, hpQ, hpR]
        simp
      have hrw : (∏ j ∈ insert a S, W j) * ((∏ j ∈ insert a S, W j) * R)
          = W a * (W a * (Q * (Q * R))) := by
        rw [Finset.prod_insert ha, ← hQ]
        ring
      rw [hrw, hWa.2 _ hpQQR, ih hWS hRS, Finset.prod_insert ha]
      push_cast
      ring
