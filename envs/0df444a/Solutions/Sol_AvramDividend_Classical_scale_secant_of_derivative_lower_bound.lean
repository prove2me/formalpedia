-- Prove2me | solution 1 for AvramDividend.Classical.scale_secant_of_derivative_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:26:27.146316+00:00
-- url     : https://prove2.me/submissions/ecd8302d-d233-4e96-924b-72898663b361

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (c d : ℝ)
    (hcont : ContinuousOn W (Set.Icc 0 c))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 c))
    (hderiv : ∀ t ∈ Set.Ioo 0 c, d ≤ deriv W t) :
    ∀ b x : ℝ, 0 ≤ b → b ≤ x → x ≤ c →
      (x - b) * d ≤ W x - W b := by
  intro b x hb hbx hxc
  have hf : DifferentiableOn ℝ W (interior (Set.Icc 0 c)) := by
    simpa only [interior_Icc] using hdiff
  have hd : ∀ t ∈ interior (Set.Icc 0 c), d ≤ deriv W t := by
    simpa only [interior_Icc] using hderiv
  simpa only [mul_comm] using
    (convex_Icc (0 : ℝ) c).mul_sub_le_image_sub_of_le_deriv hcont hf hd
      b ⟨hb, hbx.trans hxc⟩ x ⟨hb.trans hbx, hxc⟩ hbx
