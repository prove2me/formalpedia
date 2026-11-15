-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a288_combined_small_discount_Young_second_energy_cross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:18:37.980749+00:00
-- url     : https://prove2.me/submissions/9d75a3c3-f527-40d6-8665-93b54d49ca37

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (q s Δ u v d h r z ε L M η : ℝ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hη : 0 < η)
    (hTaylor : max (Real.exp (-(q*s)) *
      (v-u-d*r-h/2*r^2)) 0 ≤ ε*r^2)
    (hLip : |v-u| ≤ L*|r|) (hh : |h| ≤ M) :
    max (Real.exp (-(q*(s+Δ))) * (v-u) -
      Real.exp (-(q*s)) * (d*r+h/2*z^2)) 0 ≤
      (ε+η)*r^2+(q*Δ*L)^2/(4*η)+M/2*|r^2-z^2| := by
  have hS := avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
    q s Δ u v d h r z ε L M hq hs hΔ hε hL hM
    hTaylor hLip hh
  have hY := avram_ga_a281_discount_raw_first_increment_Young_square_budget
    η (q*Δ) L r hη (mul_nonneg hq hΔ) hL
  nlinarith
