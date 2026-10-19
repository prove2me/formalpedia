-- Prove2me | solution 1 for CohnElkies.saddleNegative_relativeGammaTail_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/16b23015-604e-41fe-b4ed-876ba05349af

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_gamma_half_factorial_lower
import Theorems.Thm_CohnElkies_saddleNegative_factorialTail_le_majorant
import Theorems.Thm_CohnElkies_saddleNegative_sqrt_le_one_add

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {C K Kε ℓ y : ℝ}
    (hKε : 0 ≤ Kε)
    (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ)
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
      (Kε * Real.sqrt y *
          y ^ saddleSmallResidueTruncation ℓ /
            Real.Gamma
              ((saddleSmallResidueTruncation ℓ : ℝ) + 3 / 2) *
        Real.exp
          (K *
            (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
              ℓ)) ≤
      saddleNegativeRelativeGammaTailMajorant C K Kε ℓ := by
  let N : ℕ := saddleSmallResidueTruncation ℓ
  let Y : ℝ := Real.log ℓ / 8 + C
  have hY : 0 ≤ Y := by
    try dsimp [Y]
    exact add_nonneg
      (div_nonneg (Real.log_nonneg hℓ) (by norm_num)) hC
  have hΓ : 0 < Real.Gamma (3 / 2 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hfactorial : 0 < (N.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hq : 0 < Real.Gamma ((N : ℝ) + 3 / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hfrac :
      y ^ N / Real.Gamma ((N : ℝ) + 3 / 2) ≤
        (y ^ N / (N.factorial : ℝ)) /
          Real.Gamma (3 / 2 : ℝ) := by
    calc
      y ^ N / Real.Gamma ((N : ℝ) + 3 / 2) ≤
          y ^ N /
            (Real.Gamma (3 / 2 : ℝ) * (N.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (pow_nonneg hy N)
          (mul_pos hΓ hfactorial)
          (gamma_half_factorial_lower N)
      _ = (y ^ N / (N.factorial : ℝ)) /
          Real.Gamma (3 / 2 : ℝ) := by
        field_simp [hΓ.ne', hfactorial.ne']
  have hsqrt := saddleNegative_sqrt_le_one_add hy
  have hsqrtY : Real.sqrt y ≤ 1 + Y := by
    calc
      Real.sqrt y ≤ 1 + y := hsqrt
      _ ≤ 1 + Y := by dsimp [Y]; linarith
  have htail :=
    saddleNegative_factorialTail_le_majorant hy hyupper
  have hbase : 0 ≤ y ^ N / (N.factorial : ℝ) := by
    positivity
  have hmajor : 0 ≤ saddleSmallResidueTailMajorant C ℓ := by
    unfold saddleSmallResidueTailMajorant
    positivity
  let E : ℝ := Real.exp
    (K * (2 * (N : ℝ) + 1) ^ 2 / ℓ)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  change Real.exp y *
    (Kε * Real.sqrt y * y ^ N /
      Real.Gamma ((N : ℝ) + 3 / 2) * E) ≤ _
  calc
    Real.exp y *
        (Kε * Real.sqrt y * y ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) * E) =
      Kε * Real.sqrt y *
        (Real.exp y *
          (y ^ N / Real.Gamma ((N : ℝ) + 3 / 2))) * E := by
      ring
    _ ≤ Kε * Real.sqrt y *
        (Real.exp y *
          ((y ^ N / (N.factorial : ℝ)) /
            Real.Gamma (3 / 2 : ℝ))) * E := by
      gcongr
    _ = (Kε / Real.Gamma (3 / 2 : ℝ)) *
        Real.sqrt y *
          (Real.exp y * (y ^ N / (N.factorial : ℝ))) * E := by
      ring
    _ ≤ (Kε / Real.Gamma (3 / 2 : ℝ)) *
        (1 + Y) *
          (2 * saddleSmallResidueTailMajorant C ℓ) * E := by
      gcongr
    _ = saddleNegativeRelativeGammaTailMajorant C K Kε ℓ := by
      unfold saddleNegativeRelativeGammaTailMajorant
      try dsimp [N, Y, E]
      ring
end CohnElkies
