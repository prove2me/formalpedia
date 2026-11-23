-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.measure_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:57.557154+00:00
-- url     : https://prove2.me/submissions/6d0db241-50c6-4c9a-88dc-3332c29b6fe2

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measurableAdd_mat

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
theorem _root_.solution {n a : ℕ} (ν : Measure (Matrix (Fin n) (Fin a) F)) [ν.IsAddLeftInvariant]
    (O : Subring F) (ϖ : F) (r : Matrix (Fin n) (Fin a) F) :
    ν (piece O ϖ r) = ν (IIset O ϖ) := by
  haveI := measurableAdd_mat (F := F) n a
  unfold piece
  exact measure_preimage_add ν (-r) _
end Formalism.DoubleCosetMeasures.P.Vol
