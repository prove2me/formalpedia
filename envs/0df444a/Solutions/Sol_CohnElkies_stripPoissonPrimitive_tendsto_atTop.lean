-- Prove2me | solution 1 for CohnElkies.stripPoissonPrimitive_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/ec1f7a4d-cae9-437c-8224-d224bd6e8800

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    Tendsto (stripPoissonPrimitive σ) atTop (nhds (1 / 2 : ℝ)) := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hscale : Tendsto (fun T : ℝ => Real.pi * T / 2) atTop atTop := by
    convert! tendsto_id.atTop_mul_const (half_pos Real.pi_pos) using 1
    ext T
    change Real.pi * T / 2 = T * (Real.pi / 2)
    ring
  have hexp : Tendsto (fun T : ℝ => Real.exp (Real.pi * T / 2))
      atTop atTop := Real.tendsto_exp_atTop.comp hscale
  have hshift : Tendsto
      (fun T : ℝ => Real.exp (Real.pi * T / 2) -
        Real.cos (stripAngle σ)) atTop atTop := by
    simpa [sub_eq_add_neg] using!
      (tendsto_atTop_add_const_right atTop
        (-Real.cos (stripAngle σ)) hexp)
  have hratio : Tendsto
      (fun T : ℝ =>
        (Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)) /
          Real.sin (stripAngle σ)) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hsin).2 hshift
  have hatan : Tendsto
      (fun T : ℝ =>
        Real.arctan
          ((Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)) /
            Real.sin (stripAngle σ)))
      atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      hratio
  unfold stripPoissonPrimitive
  convert! hatan.div_const Real.pi using 1
  field_simp [Real.pi_ne_zero]
end CohnElkies
