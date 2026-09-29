-- Prove2me | solution 1 for Finset.ruzsa_sumset_to_difference
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:45.29962+00:00
-- url     : https://prove2.me/submissions/de12c054-d84f-4196-80c0-9496bbf4f90b

import Mathlib

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ K c : ℝ, 0 < K → 0 < c → ∀ A B : Finset G, A.Nonempty → B.Nonempty →
      ((A + B).card : ℝ) ≤ K * A.card →
      c * (A.card : ℝ) ≤ (B.card : ℝ) →
      ((A - B).card : ℝ) ≤ K ^ 3 / c * A.card := by
  intro K c hK hc A B hA hB hAB hcB
  -- Positivity facts
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hAne : (A.card : ℝ) ≠ 0 := ne_of_gt hApos
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  -- Step 1: Plünnecke-Ruzsa gives |B + B| ≤ K² · |A|.
  have hPR : ((2 • B).card : ℚ≥0)
      ≤ (((A + B).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) :=
    Finset.pluennecke_ruzsa_inequality_nsmul_add hA B 2
  have h2B : (2 : ℕ) • B = B + B := two_nsmul B
  rw [h2B] at hPR
  -- Cast hPR from ℚ≥0 to ℝ by first going to ℚ then to ℝ via NNRat.cast_divNat.
  have hPR_real : ((B + B).card : ℝ)
      ≤ (((A + B).card : ℝ) / (A.card : ℝ)) ^ 2 * (A.card : ℝ) := by
    have hQ : ((B + B).card : ℝ)
        ≤ ((((A + B).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) : ℝ) := by
      exact_mod_cast hPR
    simpa using hQ
  have hAB_div : ((A + B).card : ℝ) / (A.card : ℝ) ≤ K :=
    (div_le_iff₀ hApos).mpr hAB
  have hAB_div_nn : 0 ≤ ((A + B).card : ℝ) / (A.card : ℝ) :=
    div_nonneg (by positivity) (le_of_lt hApos)
  have hBB_le : ((B + B).card : ℝ) ≤ K ^ 2 * (A.card : ℝ) := by
    refine hPR_real.trans ?_
    have hsq : (((A + B).card : ℝ) / (A.card : ℝ)) ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ hAB_div_nn hAB_div 2
    exact mul_le_mul_of_nonneg_right hsq (le_of_lt hApos)
  -- Step 2: Ruzsa triangle: |A - B| · |B| ≤ |A + B| · |B + B|
  have hRTℕ : (A - B).card * B.card ≤ (A + B).card * (B + B).card :=
    Finset.ruzsa_triangle_inequality_sub_add_add A B B
  have hRT : ((A - B).card : ℝ) * (B.card : ℝ)
      ≤ ((A + B).card : ℝ) * ((B + B).card : ℝ) := by exact_mod_cast hRTℕ
  -- Step 3: chain bounds → |A-B| · |B| ≤ K³ · |A|²
  have hBBnn : 0 ≤ ((B + B).card : ℝ) := by positivity
  have hKA_nn : 0 ≤ K * (A.card : ℝ) := mul_nonneg (le_of_lt hK) (le_of_lt hApos)
  have hChain : ((A + B).card : ℝ) * ((B + B).card : ℝ)
      ≤ (K * A.card) * (K ^ 2 * A.card) :=
    mul_le_mul hAB hBB_le hBBnn hKA_nn
  have hKcube : (K * (A.card : ℝ)) * (K ^ 2 * A.card) = K ^ 3 * (A.card : ℝ) ^ 2 := by
    ring
  have hdiff_mul_B : ((A - B).card : ℝ) * (B.card : ℝ)
      ≤ K ^ 3 * (A.card : ℝ) ^ 2 := by
    rw [← hKcube]; exact hRT.trans hChain
  -- Step 4: use c · |A| ≤ |B| to replace |B| on the LHS
  have hdiff_nn : 0 ≤ ((A - B).card : ℝ) := by positivity
  have hdiff_mul_cA : ((A - B).card : ℝ) * (c * A.card)
      ≤ K ^ 3 * (A.card : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left hcB hdiff_nn).trans hdiff_mul_B
  -- Step 5: divide both sides by c · |A| > 0
  have hcA_pos : (0 : ℝ) < c * A.card := mul_pos hc hApos
  rw [show K ^ 3 / c * (A.card : ℝ) = K ^ 3 * (A.card : ℝ) ^ 2 / (c * A.card) by
        field_simp]
  rw [le_div_iff₀ hcA_pos]
  linarith [hdiff_mul_cA]
