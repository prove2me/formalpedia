-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_locS_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:00.013452+00:00
-- url     : https://prove2.me/submissions/f650b451-1aa3-490d-831f-0dfa5eeb98c1

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_span_top
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution {e : Fin d → Fin d → K} (he : LinearIndependent K e) :
    locS (nonZeroDivisors R) (Submodule.span R (Set.range e)) = ⊤ := by
  apply indexBasic_locS_top (K := K)
  rw [Submodule.span_span_of_tower]
  exact idxChange_span_top he
end Formalism.DivisionValues
