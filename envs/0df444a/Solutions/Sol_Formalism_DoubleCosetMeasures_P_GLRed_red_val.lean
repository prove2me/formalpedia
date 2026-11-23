-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.red_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:16.102349+00:00
-- url     : https://prove2.me/submissions/bbae10a1-2da3-44e5-bb66-468396b87bf1

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
namespace Formalism.DoubleCosetMeasures.P.GLRed
theorem _root_.solution (g : GLint O a) (i j : Fin a) :
    ((red O a ϖ hϖ g : GL (Fin a) (kF O ϖ hϖ)) : Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) i j =
      Ideal.Quotient.mk _ ⟨((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j, g.2.1 i j⟩ :=
  rfl
end Formalism.DoubleCosetMeasures.P.GLRed
