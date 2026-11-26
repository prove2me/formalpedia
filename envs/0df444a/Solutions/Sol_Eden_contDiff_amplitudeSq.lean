-- Prove2me | solution 1 for Eden.contDiff_amplitudeSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:21.915798+00:00
-- url     : https://prove2.me/submissions/de805123-eaad-468e-a376-f498ee8f7d80

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
import Theorems.Thm_Eden_radialDiscriminant_pos
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (amplitudeSq t) := by
  have hd : ContDiff ℝ n (radialDiscriminant t) := by
    unfold radialDiscriminant
    fun_prop
  have hr := hd.sqrt (fun s => ne_of_gt (radialDiscriminant_pos ht s))
  have hR : ∀ s, Real.sqrt (radialDiscriminant t s) ≠ 0 :=
    fun s => ne_of_gt (sqrt_radialDiscriminant_pos ht s)
  have hR1 : ∀ s, Real.sqrt (radialDiscriminant t s) + 1 ≠ 0 :=
    fun s => ne_of_gt (by positivity)
  unfold amplitudeSq
  exact (contDiff_const.add
    (((contDiff_id.sub contDiff_const).mul contDiff_const).div
      (hr.add contDiff_const) hR1)).div hr hR
end Eden
