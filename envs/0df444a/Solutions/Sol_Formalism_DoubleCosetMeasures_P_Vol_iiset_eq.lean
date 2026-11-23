-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.iiset_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:43.980804+00:00
-- url     : https://prove2.me/submissions/27316ade-7c04-498f-894b-5db0500c323b

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard

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
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (ϖ : F) (hϖ0 : ϖ ≠ 0) {n a : ℕ} :
    (IIset O ϖ : Set (Matrix (Fin n) (Fin a) F)) = {y | ∀ i j, ϖ⁻¹ * y i j ∈ O} := by
  ext y
  simp only [IIset, Set.mem_setOf_eq]
  refine forall₂_congr fun i j => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
  · rintro ⟨o, ho, e⟩
    rw [e, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
    exact ho
  · rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
end Formalism.DoubleCosetMeasures.P.Vol
