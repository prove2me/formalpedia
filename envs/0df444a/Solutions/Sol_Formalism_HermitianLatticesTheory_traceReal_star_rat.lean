-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.traceReal_star_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:00.610864+00:00
-- url     : https://prove2.me/submissions/62ffc8f3-5e63-484e-9e5a-52fb1b022ede

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Definitions.Def_Lemmata_GeneralBFactSecondSide_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (q : ℚ) : starRingEnd K (algebraMap ℚ K q) = algebraMap ℚ K q := by
  rw [eq_ratCast (algebraMap ℚ K) q, map_ratCast]
end Formalism.HermitianLatticesTheory
