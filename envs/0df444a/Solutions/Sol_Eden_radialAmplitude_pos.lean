-- Prove2me | solution 1 for Eden.radialAmplitude_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:02.077582+00:00
-- url     : https://prove2.me/submissions/0b1c92e8-31cd-4400-a142-4c2bb237deac

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < radialAmplitude t s := by
  exact div_pos (Real.exp_pos _)
    (mul_pos (planarAmplitude_pos ht hs)
      (pow_pos (sqrt_radialDiscriminant_pos ht s) 3))
end Eden
