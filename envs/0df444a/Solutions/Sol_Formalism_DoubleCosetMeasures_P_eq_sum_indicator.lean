-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:44.055833+00:00
-- url     : https://prove2.me/submissions/c2d451c1-5c17-4848-a26f-1c7b382c35ac

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_cls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {X : Type}
variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (r : Setoid X) (f : X → E)
    (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (t : Finset (Quotient r)) (ht : Function.support (fun q : Quotient r => f q.out) ⊆ t) :
    f = fun x => ∑ q ∈ t, (cls r q).indicator (fun _ => f q.out) x := by
  classical
  funext x
  have hx : f x = f (Quotient.mk r x).out := hf _ _ (Quotient.out_eq _).symm
  simp only [Set.indicator_apply, mem_cls]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact hx
  · rw [hx]
    by_contra hne
    exact h (ht hne)
end Formalism.DoubleCosetMeasures.P
