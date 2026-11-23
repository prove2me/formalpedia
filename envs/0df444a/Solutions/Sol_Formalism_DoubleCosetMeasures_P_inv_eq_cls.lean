-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.inv_eq_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:44.167134+00:00
-- url     : https://prove2.me/submissions/0a42b73a-74df-4d14-848a-0be53edef1c0

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_preimage_rightRel_mk
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_preimage_leftQuot_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    {E : Type} (f : G₁ × G₂ → E)
    (hf : ∀ a ∈ K₁, ∀ b ∈ K₂, ∀ x : G₁, ∀ y : G₂, f (a * x, y * b) = f (x, y)) (z : G₁ × G₂) :
    f z = f ((clsTS K₁ K₂ z).1.out, (clsTS K₁ K₂ z).2.out) := by
  have h1 := (mem_preimage_rightRel_mk K₁ (Quotient.mk (QuotientGroup.rightRel K₁) z.1) z.1).1 rfl
  have h2 := (mem_preimage_leftQuot_mk K₂ (z.2 : G₂ ⧸ K₂) z.2).1 rfl
  have h := hf _ h1 _ h2 (Quotient.mk (QuotientGroup.rightRel K₁) z.1).out (z.2 : G₂ ⧸ K₂).out
  simp only [inv_mul_cancel_right, mul_inv_cancel_left] at h
  simpa [clsTS] using h
end Formalism.DoubleCosetMeasures.P
