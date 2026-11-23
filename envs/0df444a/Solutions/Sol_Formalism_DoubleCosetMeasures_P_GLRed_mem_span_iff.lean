-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.mem_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:01.751621+00:00
-- url     : https://prove2.me/submissions/370e26f9-27ba-4a6f-9198-d06558bacdbc

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.GLRed
variable {F : Type} [Field F] (O : Subring F) {a : ℕ}
variable (a)
variable (ϖ : F) (hϖ : ϖ ∈ O)
variable {a}
namespace Formalism.DoubleCosetMeasures.P.GLRed
theorem _root_.solution (hϖ0 : ϖ ≠ 0) (x : O) :
    x ∈ Ideal.span {(⟨ϖ, hϖ⟩ : O)} ↔ ϖ⁻¹ * (x : F) ∈ O := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    have : (x : F) = c * ϖ := by rw [← hc]; rfl
    rw [this, mul_comm (c : F), ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    change ϖ⁻¹ * (x : F) * ϖ = x
    field_simp
end Formalism.DoubleCosetMeasures.P.GLRed
