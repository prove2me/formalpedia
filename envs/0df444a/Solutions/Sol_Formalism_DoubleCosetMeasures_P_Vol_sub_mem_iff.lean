-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.sub_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:24.808519+00:00
-- url     : https://prove2.me/submissions/11380950-21fb-4421-ae49-cfc734266fc6

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
theorem _root_.solution {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {x y : F} (hx : x ∈ O) (hy : y ∈ O) :
    (∃ o ∈ O, x - y = ϖ * o) ↔
      (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨x, hx⟩ =
        Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨y, hy⟩) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨o, ho, e⟩
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    show o * ϖ = x - y
    rw [e, mul_comm]
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    have h1 := congrArg Subtype.val hc
    change (c : F) * ϖ = x - y at h1
    rw [← h1, mul_comm]
end Formalism.DoubleCosetMeasures.P.Vol
