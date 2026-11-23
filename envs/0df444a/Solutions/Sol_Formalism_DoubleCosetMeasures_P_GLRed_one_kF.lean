-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.one_kF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:34.374606+00:00
-- url     : https://prove2.me/submissions/883eef10-c46b-4f70-9309-ef07c3009e42

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
theorem _root_.solution (i j : Fin a) : (1 : Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) i j =
    Ideal.Quotient.mk _ ((1 : Matrix (Fin a) (Fin a) O) i j) := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
end Formalism.DoubleCosetMeasures.P.GLRed
