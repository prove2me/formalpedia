-- Prove2me | solution 1 for CohnElkies.integrable_exp_neg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/fe426e29-08ea-4fe7-9eea-4438b4b9ba29

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    Integrable (fun T : ℝ => Real.exp (-a * |T|)) := by
  have hright :
      IntegrableOn (fun T : ℝ => Real.exp (-a * |T|))
        (Ioi (0 : ℝ)) := by
    have h := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
    apply h.congr_fun _ measurableSet_Ioi
    intro T hT
    change Real.exp (-a * T) = Real.exp (-a * |T|)
    rw [abs_of_pos hT]
  have hleft :
      IntegrableOn (fun T : ℝ => Real.exp (-a * |T|))
        (Iio (0 : ℝ)) := by
    have h := (integrableOn_exp_mul_Iic ha 0).mono_set
      (show Iio (0 : ℝ) ⊆ Iic (0 : ℝ) from
        fun _ hT => (mem_Iio.mp hT).le)
    apply h.congr_fun _ measurableSet_Iio
    intro T hT
    change Real.exp (a * T) = Real.exp (-a * |T|)
    rw [abs_of_neg hT]
    congr 1
    ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩
end CohnElkies
