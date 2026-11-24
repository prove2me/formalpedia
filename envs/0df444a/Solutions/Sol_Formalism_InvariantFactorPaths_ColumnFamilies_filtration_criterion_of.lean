-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_criterion_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:37:06.667582+00:00
-- url     : https://prove2.me/submissions/ebe6afe6-dbb0-449e-8f35-7f92a4f999e8

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationGenericPointCriterion
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_mem_span_standard_iff_proj_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → FiltrationGenericPointCriterion :=
  fun hA n _ M CF pi hpi F _ x => mem_span_standard_iff_proj_zero hA CF pi hpi F x
end Formalism.InvariantFactorPaths.ColumnFamilies
