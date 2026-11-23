-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.intRightInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:18.019927+00:00
-- url     : https://prove2.me/submissions/8ef4fa1d-a959-4c6b-bce0-94128267ea0d

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_support_out_finite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_integral_eq_finsum
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_leftRel

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
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.IntRightInv := by
  intro G _ _ _ _ _ μ _ K₀ hK E _ _ _ f hf hc
  have hr : ∀ q, IsOpen (cls (QuotientGroup.leftRel K₀) q) := fun q => by
    rw [cls_leftRel]; exact hK.preimage (continuous_const.mul continuous_id)
  have hμq : ∀ q : G ⧸ K₀, μ (cls (QuotientGroup.leftRel K₀) q) = μ (K₀ : Set G) := fun q => by
    rw [cls_leftRel, measure_preimage_mul]
  have hf' : ∀ x y : G, Quotient.mk (QuotientGroup.leftRel K₀) x =
      Quotient.mk (QuotientGroup.leftRel K₀) y → f x = f y := by
    intro x y h
    have h' : (x : G ⧸ K₀) = (y : G ⧸ K₀) := h
    rw [QuotientGroup.eq] at h'
    have := hf x _ h'
    rw [mul_inv_cancel_left] at this
    exact this.symm
  refine ⟨support_out_finite _ hr f hc, ?_⟩
  rw [integral_eq_finsum _ hr μ f hf' hc]
  · exact finsum_congr fun q => by rw [hμq]
  · by_cases h : μ (K₀ : Set G) < ⊤
    · exact Or.inl fun q => (hμq q).symm ▸ h
    · exact Or.inr fun q => (hμq q).trans (not_lt_top_iff.1 h)
end Formalism.DoubleCosetMeasures.P
