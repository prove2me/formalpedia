-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.exists_position_small
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:59.143272+00:00
-- url     : https://prove2.me/submissions/7373ecda-0d96-4673-bbf1-ed02a9e55fe3

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.exists_position_small
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Theorems.Thm_BookProof_SqueezedGaussStates_coordComboSum_opCoef_le
import Theorems.Thm_BookProof_SqueezedGaussStates_tendsto_boundary
import Theorems.Thm_BookProof_GaussCoordCombo_coordComboSum_nonneg
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : ℝ) (M : ℕ), 4 * v ^ 2 < 1 ∧
      coordComboSum (opCoef 1 0 v M) 1 M ≤ ε * coordComboSum (sqCoef v M) 0 M := by

  obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ε / 2 :=
    ⟨min (ε / 2) (1 / 2), by positivity, by
      have : min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
      linarith, min_le_left _ _⟩
  set v : ℝ := -((1 - δ) / 2) with hv
  have hvsq : 4 * v ^ 2 = (1 - δ) ^ 2 := by rw [hv]; ring
  have hρ0 : (0 : ℝ) ≤ (1 - δ) ^ 2 := sq_nonneg _
  have hρ1 : (1 - δ) ^ 2 < 1 := by nlinarith
  have hvlt : 4 * v ^ 2 < 1 := by rw [hvsq]; exact hρ1
  have hden : 0 < 1 - 4 * v ^ 2 := by linarith
  have hkap : kappa 1 0 v = δ := by rw [kappa, hv]; ring
  have hratio : (kappa 1 0 v) ^ 2 / (1 - 4 * v ^ 2) ≤ ε / 2 := by
    rw [hkap, hvsq]
    have hd : 1 - (1 - δ) ^ 2 = δ * (2 - δ) := by ring
    rw [hd, div_le_iff₀ (by nlinarith)]
    nlinarith
  -- choose `M` large enough to kill the boundary term
  have hlim := tendsto_boundary ((1 - δ) ^ 2) hρ0 hρ1
  have hev : ∀ᶠ M : ℕ in Filter.atTop, (2 * (M : ℝ) + 1) * ((1 - δ) ^ 2) ^ M < ε / 2 := by
    have := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
    exact this
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨v, M, hvlt, ?_⟩
  have hmain := coordComboSum_opCoef_le 1 0 v M hvlt
  have hVpos : 0 ≤ coordComboSum (sqCoef v M) 0 M := coordComboSum_nonneg _ _ _
  have hcoef : (kappa 1 0 v) ^ 2 / (1 - 4 * v ^ 2)
      + (1 : ℝ) ^ 2 * (2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M ≤ ε := by
    rw [hvsq]
    have : (1 : ℝ) ^ 2 * (2 * (M : ℝ) + 1) * ((1 - δ) ^ 2) ^ M
        = (2 * (M : ℝ) + 1) * ((1 - δ) ^ 2) ^ M := by ring
    rw [this]
    have h2 : (kappa 1 0 v) ^ 2 / (1 - 4 * v ^ 2) ≤ ε / 2 := hratio
    rw [hvsq] at h2
    linarith
  calc coordComboSum (opCoef 1 0 v M) 1 M
      ≤ ((kappa 1 0 v) ^ 2 / (1 - 4 * v ^ 2)
          + (1 : ℝ) ^ 2 * (2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M)
        * coordComboSum (sqCoef v M) 0 M := hmain
    _ ≤ ε * coordComboSum (sqCoef v M) 0 M := mul_le_mul_of_nonneg_right hcoef hVpos
