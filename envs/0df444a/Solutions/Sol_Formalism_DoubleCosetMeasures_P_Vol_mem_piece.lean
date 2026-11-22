-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:22:20.439696+00:00
-- url     : https://prove2.me/submissions/8d88f17b-6529-40b8-9cef-544c449aaf89

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
theorem _root_.solution {O : Subring F} {ϖ : F} {n a : ℕ} {r y : Matrix (Fin n) (Fin a) F} :
    y ∈ piece O ϖ r ↔ ∀ i j, ∃ o ∈ O, y i j - r i j = ϖ * o := by
  simp only [piece, Set.mem_preimage, IIset, Set.mem_setOf_eq, Matrix.add_apply,
    Matrix.neg_apply, neg_add_eq_sub, Matrix.sub_apply]
end Formalism.DoubleCosetMeasures.P.Vol
