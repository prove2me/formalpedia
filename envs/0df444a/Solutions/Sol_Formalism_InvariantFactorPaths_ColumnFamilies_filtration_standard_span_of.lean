-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_standard_span_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:21.142575+00:00
-- url     : https://prove2.me/submissions/ceb63bbd-d1cc-4afe-bfb3-5bf74b170ce8

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationStandardSpan
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_Mpi_eq


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
theorem _root_.solution : LemmaA → FiltrationStandardSpan :=
  fun hA n _ M CF pi hpi => qb_Mpi_eq hA CF pi hpi
end Formalism.InvariantFactorPaths.ColumnFamilies
