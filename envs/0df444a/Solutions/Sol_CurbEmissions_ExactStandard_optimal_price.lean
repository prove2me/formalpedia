-- Prove2me | solution 1 for CurbEmissions.ExactStandard.optimal_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:48:22.158636+00:00
-- url     : https://prove2.me/submissions/bb90fc72-9ba5-41d8-84fc-f62a8cda3a46

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model
set_option autoImplicit false
open CurbEmissions.ExactStandard

theorem solution (P : Params) (hP : Standing P) (e m : ℝ) (he : 0 ≤ e) (hm : 0 < m) :
    (∀ p, priceObj P e m p ≤ priceObj P e m (pStar P e)) ∧
    ((P.c - P.gam) * e < P.ubar →
      ∀ p, p ≠ pStar P e → priceObj P e m p < priceObj P e m (pStar P e)) := by
  obtain ⟨hc, hg, hr, hm1, hm2, hb, hh, hu, hbu⟩ := hP
  have hu0 : 0 < P.ubar := lt_of_lt_of_le (by positivity) hu
  have hcg : 0 < P.c - P.gam := by linarith
  have hobj : ∀ p, priceObj P e m p
      = (p - P.c * e) * m * min 1 (max 0 (1 - (p - P.gam * e) / P.ubar)) := by
    intro p; rfl
  have hstar : pStar P e = ((P.c + P.gam) * e + P.ubar) / 2 := rfl
  -- value of the unclamped quadratic
  have key : ∀ p : ℝ, (pStar P e - P.c * e) * m * (1 - (pStar P e - P.gam * e) / P.ubar)
      - (p - P.c * e) * m * (1 - (p - P.gam * e) / P.ubar)
      = m * (p - pStar P e) ^ 2 / P.ubar := by
    intro p
    rw [hstar]
    field_simp
    ring
  have tstar : 1 - (pStar P e - P.gam * e) / P.ubar
      = (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) := by
    rw [hstar]; field_simp; ring
  by_cases hmar : (P.c - P.gam) * e < P.ubar
  · -- positive margin
    have ht1 : 0 < (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) := by
      apply div_pos (by linarith) (by positivity)
    have ht2 : (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [mul_nonneg hcg.le he]
    have hV : priceObj P e m (pStar P e)
        = (pStar P e - P.c * e) * m * (1 - (pStar P e - P.gam * e) / P.ubar) := by
      rw [hobj, tstar, max_eq_right ht1.le, min_eq_right ht2]
    have hVpos : 0 < priceObj P e m (pStar P e) := by
      rw [hV, tstar, hstar]
      have : ((P.c + P.gam) * e + P.ubar) / 2 - P.c * e = (P.ubar - (P.c - P.gam) * e) / 2 := by ring
      rw [this]
      have hpos : 0 < P.ubar - (P.c - P.gam) * e := by linarith
      positivity
    have main : ∀ p, p ≠ pStar P e → priceObj P e m p < priceObj P e m (pStar P e) := by
      intro p hp
      rcases lt_or_ge (1 - (p - P.gam * e) / P.ubar) 0 with h0 | h0
      · rw [hobj, max_eq_left h0.le, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
        simp only [mul_zero]
        exact hVpos
      · rcases le_or_gt (1 - (p - P.gam * e) / P.ubar) 1 with h1 | h1
        · rw [hobj, max_eq_right h0, min_eq_right h1, hV]
          have := key p
          have hsq : 0 < m * (p - pStar P e) ^ 2 / P.ubar := by
            have : p - pStar P e ≠ 0 := sub_ne_zero.2 hp
            positivity
          rw [hV] at hVpos
          linarith
        · -- share = 1, p < g e
          have hp1 : p < P.gam * e := by
            have : 0 < (p - P.gam * e) / P.ubar * (-1) := by linarith
            have h2 : (p - P.gam * e) / P.ubar < 0 := by linarith
            have := (div_neg_iff.1 h2)
            rcases this with ⟨_, h⟩ | ⟨h, _⟩
            · linarith
            · linarith
          rw [hobj, max_eq_right h0, min_eq_left h1.le]
          have : (p - P.c * e) * m * 1 ≤ 0 := by
            have : p - P.c * e < 0 := by nlinarith [mul_nonneg hcg.le he]
            nlinarith
          linarith
    refine ⟨fun p => ?_, fun _ => main⟩
    by_cases hp : p = pStar P e
    · rw [hp]
    · exact (main p hp).le
  · -- nonpositive margin: the maximal profit is 0
    have hmar := not_lt.1 hmar
    have ht : (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have hV : priceObj P e m (pStar P e) = 0 := by
      rw [hobj, tstar, max_eq_left ht, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      simp
    refine ⟨fun p => ?_, fun h => absurd h (not_lt.2 hmar)⟩
    rw [hV]
    rcases lt_or_ge (1 - (p - P.gam * e) / P.ubar) 0 with h0 | h0
    · rw [hobj, max_eq_left h0.le, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      simp
    · rw [hobj, max_eq_right h0]
      have hpl : p ≤ P.ubar + P.gam * e := by
        have : (p - P.gam * e) / P.ubar ≤ 1 := by linarith
        rw [div_le_one hu0] at this
        linarith
      have hpc : p - P.c * e ≤ 0 := by nlinarith
      have hmn : 0 ≤ min 1 (1 - (p - P.gam * e) / P.ubar) := le_min (by norm_num) h0
      have : (p - P.c * e) * m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpc hm.le
      exact mul_nonpos_of_nonpos_of_nonneg this hmn
