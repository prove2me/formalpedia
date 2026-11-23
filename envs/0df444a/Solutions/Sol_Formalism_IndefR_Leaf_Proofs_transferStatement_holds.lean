-- Prove2me | solution 1 for Formalism.IndefR.Leaf.Proofs.transferStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:05.256562+00:00
-- url     : https://prove2.me/submissions/6d6b0bea-db8b-4a24-9628-22c37190a2d1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_Unimod
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_UnimodP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Leaf Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory
namespace Formalism.IndefR.Leaf.Proofs
theorem _root_.solution : HaarRightInvTransfer := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ e h ν hν
  have hμ : (ν.map e.symm).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν e.symm
  have hr : (ν.map e.symm).IsMulRightInvariant := h _ hμ
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hν' : ν = (ν.map e.symm).map e := by
    rw [Measure.map_map he hes]
    have : (e : G → H) ∘ e.symm = id := funext fun x => e.apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  rw [hν', Measure.map_map (measurable_mul_const g) he]
  have hc : (fun x => x * g) ∘ (e : G → H) = (e : G → H) ∘ (fun x => x * e.symm g) := by
    funext x; simp [map_mul]
  rw [hc, ← Measure.map_map he (measurable_mul_const _), hr.map_mul_right_eq_self (e.symm g)]
end Formalism.IndefR.Leaf.Proofs
