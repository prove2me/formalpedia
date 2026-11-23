-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.isOpen_intSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:33.669183+00:00
-- url     : https://prove2.me/submissions/59157da4-59e2-4530-b8ca-e3e4bf0934ef

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isOpen_isInt_set

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (R : Subring K) (hR : IsOpen (R : Set K)) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) : IsOpen (intSub R H : Set H) := by
  exact (isOpen_isInt_set R hR n).preimage continuous_subtype_val
end Formalism.DoubleCosetMeasures.P
