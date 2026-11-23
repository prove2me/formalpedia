-- Prove2me | solution 1 for Formalism.ELL.expWeight_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:08.820866+00:00
-- url     : https://prove2.me/submissions/63c764f1-28c6-4706-a433-09d672c21a29

import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExpWeight
import Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_inv_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.G
namespace Formalism.ELL
theorem _root_.solution (h : LogWeight.{u}) : ExpWeight.{u} := by
  intro K _ _ _ p q hp hp0 hp1 hq F e l E he hei he1 hegap hlog hE0 _hEl hlE n hn
  have hlw := h K p q hp hp0 hp1 hq F e l he hei he1 hegap hlog
  have hr0 : 0 < ‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1)) := Real.rpow_pos_of_pos hp0 _
  have key : ∀ m : ℕ, (‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1)))⁻¹ *
      (‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1))) ^ m =
        ‖(p : K)‖ ^ (-((m : ℝ) - 1) / ((q : ℝ) - 1)) := by
    intro m
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_neg hp0.le,
      ← Real.rpow_add hp0]
    congr 1
    ring
  have := ExponentialCoefficientWeight.inv_le hr0 hE0 hlog.2.1
    (fun m hm => by rw [key m]; exact hlw m (by omega)) hlE n hn
  rwa [key n] at this
end Formalism.ELL
