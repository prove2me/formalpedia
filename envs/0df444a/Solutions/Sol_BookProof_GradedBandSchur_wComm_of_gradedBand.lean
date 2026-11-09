-- Prove2me | solution 1 for BookProof.GradedBandSchur.wComm_of_gradedBand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T16:48:32.001111+00:00
-- url     : https://prove2.me/submissions/388d40b2-af12-4f52-9be3-fd71e0f4883c

-- Generated from ChapterGradedBandSchurEsa.lean — solution of BookProof.GradedBandSchur.wComm_of_gradedBand
import Mathlib
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Theorems.Thm_BookProof_GradedBandSchur_degW_ge_one
import Theorems.Thm_BookProof_GradedBandSchur_degW_pos
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.GradedBandSchur




open BookProof.FockSecondQuantization BookProof.FockSchur BookProof.FockWeightedSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hC : 0 ≤ C)
    (hcard : ∀ k, (col k).support.card ≤ M)
    (hband : ∀ k, ∀ j ∈ (col k).support, ((deg j : ℤ) - (deg k : ℤ)).natAbs ≤ D)
    (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) :
    WCommBound (degW deg) col (C * M * D * (D + 2)) := by

  intro k
  set w := degW deg with hw
  have hterm : ∀ j ∈ (col k).support,
      ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ C * D * (D + 2) := by
    intro j hj
    have hwk : 0 < w k := degW_pos deg k
    have hwj : 0 < w j := degW_pos deg j
    have hwj1 : 1 ≤ w j := degW_ge_one deg j
    have hentkj : ‖(col k) j‖ ≤ C * w k := by simpa [hw, degW] using hent k j
    have hbandkj := hband k j hj
    have hdiff : |w j - w k| ≤ (D : ℝ) := by
      have h1 : |((deg j : ℤ) - (deg k : ℤ))| ≤ (D : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hbandkj
      obtain ⟨hl, hr⟩ := abs_le.mp h1
      have hl' : -(D : ℝ) ≤ (deg j : ℝ) - (deg k : ℝ) := by exact_mod_cast hl
      have hr' : (deg j : ℝ) - (deg k : ℝ) ≤ (D : ℝ) := by exact_mod_cast hr
      have : |(deg j : ℝ) - (deg k : ℝ)| ≤ (D : ℝ) := abs_le.mpr ⟨hl', hr'⟩
      have hwdiff : w j - w k = (deg j : ℝ) - (deg k : ℝ) := by
        simp only [hw, degW]; ring
      rw [hwdiff]
      exact this
    have hsplit : |w j ^ 2 - w k ^ 2| = |w j - w k| * (w j + w k) := by
      have : w j ^ 2 - w k ^ 2 = (w j - w k) * (w j + w k) := by ring
      rw [this, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ w j + w k)]
    have hwkle : w k ≤ w j + D := by
      have := abs_le.mp hdiff
      linarith [this.1, this.2]
    have hnum : ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| ≤ (C * w k) * ((D : ℝ) * (w j + w k)) := by
      refine mul_le_mul hentkj ?_ (abs_nonneg _) (mul_nonneg hC hwk.le)
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hdiff (by linarith)
    rw [div_le_iff₀ (mul_pos hwk hwj)]
    have hD0 : (0:ℝ) ≤ (D : ℝ) := by positivity
    have hsum : w j + w k ≤ ((D : ℝ) + 2) * w j := by nlinarith
    have hfac : (D : ℝ) * (w j + w k) ≤ (D : ℝ) * (((D : ℝ) + 2) * w j) :=
      mul_le_mul_of_nonneg_left hsum hD0
    have hstep : (C * w k) * ((D : ℝ) * (w j + w k)) ≤ C * D * (D + 2) * (w k * w j) := by
      calc (C * w k) * ((D : ℝ) * (w j + w k))
          ≤ (C * w k) * ((D : ℝ) * (((D : ℝ) + 2) * w j)) :=
            mul_le_mul_of_nonneg_left hfac (mul_nonneg hC hwk.le)
        _ = C * D * (D + 2) * (w k * w j) := by ring
    exact le_trans hnum hstep
  calc ∑ j ∈ (col k).support, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j)
      ≤ (col k).support.card • (C * D * (D + 2)) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (col k).support.card * (C * D * (D + 2)) := by rw [nsmul_eq_mul]
    _ ≤ M * (C * D * (D + 2)) := by
        refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard k) ?_
        have hD0 : (0:ℝ) ≤ (D : ℝ) := by positivity
        have : (0:ℝ) ≤ (D : ℝ) + 2 := by linarith
        exact mul_nonneg (mul_nonneg hC hD0) this
    _ = C * M * D * (D + 2) := by ring
