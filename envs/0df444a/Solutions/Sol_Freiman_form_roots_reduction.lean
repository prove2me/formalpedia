-- Prove2me | solution 1 for Freiman.form_roots_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:30.289026+00:00
-- url     : https://prove2.me/submissions/9a116546-8bdf-4cc6-941e-05718f6b4e93

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_root_convergent_data
import Theorems.Thm_Freiman_form_second_root_eventually_reduced
import Theorems.Thm_Freiman_form_root_coordinate_algebra

open Freiman

theorem solution (r s : ℝ) (hrs : s < r) (hr : Irrational r) (hs : Irrational s) :
    ∃ a b c d : ℤ, ∃ α β : ℝ, formUnimodular a b c d ∧
      1 < α ∧ 0 < β ∧ β < 1 ∧ Irrational α ∧ Irrational β ∧
      (c:ℝ)*α+(d:ℝ) ≠ 0 ∧ -(c:ℝ)*β+(d:ℝ) ≠ 0 ∧
      r = ((a:ℝ)*α+(b:ℝ))/((c:ℝ)*α+(d:ℝ)) ∧
      s = (-(a:ℝ)*β+(b:ℝ))/(-(c:ℝ)*β+(d:ℝ)) := by
  obtain ⟨D⟩ := form_root_convergent_data r hr
  obtain ⟨N,hN⟩ := form_second_root_eventually_reduced r s hrs D
  exact form_root_coordinate_algebra r s hs D N (hN N (le_refl N))
