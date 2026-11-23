-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.integral_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:32.913529+00:00
-- url     : https://prove2.me/submissions/cfcbd243-ef50-4e1f-a907-578622519154

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_support_out_finite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_eq_sum_indicator

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
theorem _root_.solution (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (μ : Measure X)
    (f : X → E) (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (hc : HasCompactSupport f)
    (hμ : (∀ q, μ (cls r q) < ⊤) ∨ (∀ q, μ (cls r q) = ⊤)) :
    ∫ x, f x ∂μ = ∑ᶠ q : Quotient r, (μ (cls r q)).toReal • f q.out := by
  classical
  have hfin := support_out_finite r hr f hc
  have ht : Function.support (fun q : Quotient r => f q.out) ⊆ (hfin.toFinset : Set _) := by
    simp
  have hsupp : Function.support (fun q : Quotient r => (μ (cls r q)).toReal • f q.out) ⊆
      (hfin.toFinset : Set _) := fun q hq => ht (fun h => hq (by simp [h]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rcases hμ with hμ | hμ
  · conv_lhs => rw [eq_sum_indicator r f hf hfin.toFinset ht]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ ((hr q).measurableSet)]
      rfl
    · intro q _
      exact (integrable_indicator_iff (hr q).measurableSet).2 (integrableOn_const (hμ q).ne)
  · have h0 : ∀ q, (μ (cls r q)).toReal • f q.out = 0 := fun q => by simp [hμ q]
    simp only [h0, Finset.sum_const_zero]
    by_cases hz : ∀ q : Quotient r, f q.out = 0
    · have : f = 0 := funext fun x => (hf _ _ (Quotient.out_eq _).symm).trans (hz _)
      simp [this]
    · push Not at hz
      obtain ⟨q, hq⟩ := hz
      apply integral_undef
      intro hint
      have hlt := hint.measure_norm_ge_lt_top (ε := ‖f q.out‖) (norm_pos_iff.2 hq)
      have hsub : cls r q ⊆ {x | ‖f q.out‖ ≤ ‖f x‖} := fun x hx => by
        show ‖f q.out‖ ≤ ‖f x‖
        rw [hf x q.out (hx.trans (Quotient.out_eq q).symm)]
      exact absurd (hμ q) ((measure_mono hsub).trans_lt hlt).ne
end Formalism.DoubleCosetMeasures.P
