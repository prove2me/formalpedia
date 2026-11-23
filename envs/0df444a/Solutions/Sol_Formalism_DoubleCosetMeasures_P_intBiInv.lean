-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.intBiInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:50.071019+00:00
-- url     : https://prove2.me/submissions/bb67b5e8-4372-4d2f-b997-453426d0a327

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_support_out_finite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_integral_eq_finsum
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_relIndex_conj_ne_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_dosetVol
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_double

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
theorem _root_.solution : Formalism.DoubleCosetMeasures.IntBiInv := by
  intro G _ _ _ _ _ μ _ K₀ hK hc E _ _ _ f hf hcs
  have hr : ∀ q, IsOpen (cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q) := fun q => by
    rw [cls_double]
    exact hK.mul_left
  have hμq : ∀ q, μ (cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q) =
      ((K₀.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex K₀ : ENNReal) *
        μ (K₀ : Set G) := fun q => by
    rw [cls_double]; exact (dosetVol G μ K₀ hK hc _).2
  have hf' : ∀ x y : G, Quotient.mk (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) x =
      Quotient.mk (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) y → f x = f y := by
    intro x y h
    obtain ⟨a, ha, b, hb, rfl⟩ := (DoubleCoset.eq K₀ K₀ x y).1 h
    exact (hf a ha b hb x).symm
  refine ⟨support_out_finite _ hr f hcs, ?_⟩
  rw [integral_eq_finsum _ hr μ f hf' hcs]
  · exact finsum_congr fun q => by rw [hμq, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  · by_cases h : μ (K₀ : Set G) < ⊤
    · exact Or.inl fun q => (hμq q).symm ▸ ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h
    · refine Or.inr fun q => ?_
      rw [hμq, not_lt_top_iff.1 h]
      exact ENNReal.mul_top (Nat.cast_ne_zero.2 (relIndex_conj_ne_zero K₀ hK hc _))
end Formalism.DoubleCosetMeasures.P
