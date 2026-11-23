-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:31.634312+00:00
-- url     : https://prove2.me/submissions/cc98c32f-3dc2-4727-93e6-26f8b07b6ba5

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_ker_red
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_red_surj

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
variable (a)
namespace Formalism.DoubleCosetMeasures.P.GLRed
theorem _root_.solution (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ) :
    Nat.card ((GLint O a) ⧸ (congSub O ϖ a).subgroupOf (GLint O a)) =
      Nat.card (GL (Fin a) (kF O ϖ hϖ)) := by
  rw [← ker_red O ϖ hϖ hϖ0]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (red_surj O a ϖ hϖ hloc)).toEquiv
end Formalism.DoubleCosetMeasures.P.GLRed
