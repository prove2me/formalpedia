-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.nontriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:57.758699+00:00
-- url     : https://prove2.me/submissions/ea3768bc-dd85-4883-bd89-5fb70294a839

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
theorem _root_.solution (hloc : IsLocalAt O ϖ) : Nontrivial (kF O ϖ hϖ) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton']
  rintro ⟨c, hc⟩
  have h1 : (c : F) * ϖ = 1 := congrArg Subtype.val hc
  apply hloc.1
  rw [← eq_inv_of_mul_eq_one_left h1]; exact c.2
end Formalism.DoubleCosetMeasures.P.GLRed
