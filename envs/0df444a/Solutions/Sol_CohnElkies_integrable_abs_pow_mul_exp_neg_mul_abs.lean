-- Prove2me | solution 1 for CohnElkies.integrable_abs_pow_mul_exp_neg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/1988f7dc-1cf0-49ac-85ad-ca10cd2e2ac0

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
theorem _root_.solution
    (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have hbase :
      IntegrableOn
        (fun T : ℝ => T ^ n * Real.exp (-a * T))
        (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (n : ℝ)) (b := a)
      (by exact_mod_cast (show (-(1 : ℤ) < (n : ℤ)) by omega))
      (by norm_num) ha
    simpa [Real.rpow_natCast, Real.rpow_one] using! h
  have hright :
      IntegrableOn
        (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|))
        (Ioi (0 : ℝ)) := by
    apply hbase.congr_fun _ measurableSet_Ioi
    intro T hT
    change T ^ n * Real.exp (-a * T) =
      |T| ^ n * Real.exp (-a * |T|)
    rw [abs_of_pos hT]
  have hreflected :
      IntegrableOn
        ((fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) ∘
          (fun T : ℝ => -T))
        ((fun T : ℝ => -T) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero,
      abs_neg] using! hright
  have hleft :
      IntegrableOn
        (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|))
        (Iio (0 : ℝ)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩
end CohnElkies
