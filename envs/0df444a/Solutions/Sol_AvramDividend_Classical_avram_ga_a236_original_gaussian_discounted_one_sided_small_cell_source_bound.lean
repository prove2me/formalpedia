-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:07:00.307208+00:00
-- url     : https://prove2.me/submissions/3bd9ff93-9f7e-4586-b166-d6a5844dba4d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a234_combined_fullcell_one_sided_Taylor_discount_cross_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (q s Δ u v d h r z ε L M : ℝ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hTaylor : max (Real.exp (-(q*s)) *
      (v-u-d*r-h/2*r^2)) 0 ≤ ε*r^2)
    (hLip : |v-u| ≤ L*|r|) (hh : |h| ≤ M) :
    max (Real.exp (-(q*(s+Δ))) * (v-u) -
      Real.exp (-(q*s)) * (d*r+h/2*z^2)) 0 ≤
      ε*r^2 + (q*Δ)*L*|r| + M/2*|r^2-z^2| := by
  obtain ⟨he0,he01,he1,he11,hDiff⟩ :=
    avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
      q s Δ hq hs hΔ
  exact avram_ga_a234_combined_fullcell_one_sided_Taylor_discount_cross_bound
    (Real.exp (-(q*s))) (Real.exp (-(q*(s+Δ))))
    u v d h r z ε (q*Δ) L M
    he0 he01 hε (mul_nonneg hq hΔ) hL hM
    hTaylor hDiff hLip hh
