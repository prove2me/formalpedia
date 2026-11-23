-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.meas_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:54.707723+00:00
-- url     : https://prove2.me/submissions/0ba7c70d-08a1-4b66-9876-e49b2cdad3fb

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_ii
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_add

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
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ0 : ϖ ≠ 0) {n a : ℕ}
    (r : Matrix (Fin n) (Fin a) F) : MeasurableSet (piece O ϖ r) :=
  (meas_add n a (-r)) (meas_ii O hO ϖ hϖ0 n a)
end Formalism.DoubleCosetMeasures.P.Vol
