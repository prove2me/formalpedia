-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.shear_cond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:13:48.208635+00:00
-- url     : https://prove2.me/submissions/955047f6-8641-49cc-a4ba-27e8d465b6dd

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shearMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.ShearMeasurability
variable {m : ℕ} (w : Equiv.Perm (Fin m))
namespace Formalism.FourierDecayAlt.P.ShearMeasurability
theorem _root_.solution : ShearCond (gap (m := m)) (fun x => mulMap w (eSplit w x)) := by
  intro q x y hxy
  show mulMap w (eSplit w x) q - x q = mulMap w (eSplit w y) q - y q
  rw [shearMap_apply, shearMap_apply, add_sub_cancel_left, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : q.1.2 < k
  · by_cases h2 : k < q.1.1
    · have ea : aX w x q.1.1 k = aX w y q.1.1 k := by
        unfold aX
        split_ifs with h
        · apply hxy
          rw [Fin.lt_iff_val_lt_val] at h1 h2
          show q.1.1.val - k.val < q.1.1.val - q.1.2.val
          omega
        · rfl
      have eb : bX w x k q.1.2 = bX w y k q.1.2 := by
        unfold bX
        split_ifs with h
        · apply hxy
          rw [Fin.lt_iff_val_lt_val] at h1 h2
          show k.val - q.1.2.val < q.1.1.val - q.1.2.val
          omega
        · rfl
      rw [ea, eb]
    · have h0 : ∀ z, aX w z q.1.1 k = 0 := fun z => by
        unfold aX
        rw [dif_neg (fun h => h2 h.1)]
      rw [h0, h0, zero_mul, zero_mul]
  · have h0 : ∀ z, bX w z k q.1.2 = 0 := fun z => by
      unfold bX
      rw [dif_neg (fun h => h1 h.1)]
    rw [h0, h0, mul_zero, mul_zero]
end Formalism.FourierDecayAlt.P.ShearMeasurability
