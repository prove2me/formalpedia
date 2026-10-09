-- Prove2me | solution 1 for BookProof.GaussCoordCombo.gaussInt_coordCombo_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:43:50.035609+00:00
-- url     : https://prove2.me/submissions/d57764b1-7ba8-4627-a317-1cc4bf314d9c

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.gaussInt_coordCombo_sq
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_hermiteFactor_mul
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (c : ℕ → ℝ) (p K : ℕ)
    {R : MvPolynomial (Fin d) ℂ} (hR : pderiv i R = 0) :
    gaussInt (coordCombo i c p K * (coordCombo i c p K * R))
      = ((coordComboSum c p K : ℝ) : ℂ) * gaussInt R := by

  classical
  have hexp : coordCombo i c p K * (coordCombo i c p K * R)
      = ∑ k ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
        (((c k * c l : ℝ) : ℂ)) • (hermiteFactor i (2 * k + p) * (hermiteFactor i (2 * l + p)
          * R)) := by
    simp only [coordCombo, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring_nf
  rw [hexp]
  rw [gaussInt_sum]
  have hinner : ∀ k ∈ Finset.range (K + 1),
      gaussInt (∑ l ∈ Finset.range (K + 1), (((c k * c l : ℝ) : ℂ)) •
        (hermiteFactor i (2 * k + p) * (hermiteFactor i (2 * l + p) * R)))
        = ((c k ^ 2 * ((2 * k + p).factorial : ℝ) : ℝ) : ℂ) * gaussInt R := by
    intro k hk
    rw [gaussInt_sum]
    rw [Finset.sum_eq_single k]
    · rw [gaussInt_smul, gaussInt_hermiteFactor_mul i _ _ hR, if_pos rfl]
      push_cast
      ring
    · intro l _ hl
      rw [gaussInt_smul, gaussInt_hermiteFactor_mul i _ _ hR, if_neg (by omega)]
      simp
    · intro hk'
      exact absurd hk hk'
  rw [Finset.sum_congr rfl hinner, coordComboSum]
  push_cast
  rw [Finset.sum_mul]
