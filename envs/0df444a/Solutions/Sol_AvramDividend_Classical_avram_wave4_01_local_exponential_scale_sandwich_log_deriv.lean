-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_local_exponential_scale_sandwich_log_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:31:10.384069+00:00
-- url     : https://prove2.me/submissions/f8fc6e3a-99fd-4f6e-a089-a68ac8501e3c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_two_point_slope_squeeze

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Real Set

/-- A two-point exponential scale sandwich and continuous rate give
the exact logarithmic derivative on positive reserves. -/
theorem solution
    (W κ : ℝ → ℝ)
    (hW : ∀ a : ℝ, 0 < a → 0 < W a)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hsand : ∀ a b : ℝ, 0 < a → a < b → b - a < a →
      Real.exp (-(κ a * (b - a))) ≤ W a / W b ∧
      W a / W b ≤ Real.exp (-(κ b * (b - a)))) :
    ∀ a : ℝ, 0 < a →
      HasDerivAt (fun x : ℝ => Real.log (W x)) (κ a) a := by
  have hordered : ∀ a b : ℝ, 0 < a → a < b → b - a < a →
      κ b ≤ slope (fun x : ℝ => Real.log (W x)) a b ∧
      slope (fun x : ℝ => Real.log (W x)) a b ≤ κ a := by
    intro a b ha hab hsmall
    have hb : 0 < b := lt_trans ha hab
    have hh : 0 < b - a := sub_pos.mpr hab
    have hdiv : 0 < W a / W b := div_pos (hW a ha) (hW b hb)
    obtain ⟨hlo, hhi⟩ := hsand a b ha hab hsmall
    have hloglo : -(κ a * (b - a)) ≤
        Real.log (W a / W b) := by
      simpa using Real.log_le_log (Real.exp_pos _) hlo
    have hloghi : Real.log (W a / W b) ≤
        -(κ b * (b - a)) := by
      simpa using Real.log_le_log hdiv hhi
    have hlogdiv : Real.log (W a / W b) =
        Real.log (W a) - Real.log (W b) :=
      Real.log_div (ne_of_gt (hW a ha)) (ne_of_gt (hW b hb))
    rw [hlogdiv] at hloglo hloghi
    rw [slope_def_field]
    constructor
    · apply (le_div_iff₀ hh).2
      nlinarith [hloghi]
    · apply (div_le_iff₀ hh).2
      nlinarith [hloglo]
  have hslope : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b →
      |b - a| < a / 2 →
      min (κ a) (κ b) ≤
        slope (fun x : ℝ => Real.log (W x)) a b ∧
      slope (fun x : ℝ => Real.log (W x)) a b ≤
        max (κ a) (κ b) := by
    intro a b ha hb hne hclose
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hsmall : b - a < a := by
        nlinarith [le_abs_self (b - a)]
      obtain ⟨hl, hu⟩ := hordered a b ha hab hsmall
      exact ⟨(min_le_right _ _).trans hl,
        hu.trans (le_max_left _ _)⟩
    · have hsmall : a - b < b := by
        nlinarith [neg_le_abs (b - a)]
      obtain ⟨hl, hu⟩ := hordered b a hb hba hsmall
      have hswap : slope (fun x : ℝ => Real.log (W x)) a b =
          slope (fun x : ℝ => Real.log (W x)) b a :=
        slope_comm _ a b
      rw [hswap]
      exact ⟨(min_le_left _ _).trans hl,
        hu.trans (le_max_right _ _)⟩
  exact avram_wave4_01_local_two_point_slope_squeeze
    (fun x : ℝ => Real.log (W x)) κ hκ hslope
