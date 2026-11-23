-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_span_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:20.899806+00:00
-- url     : https://prove2.me/submissions/6a3ad8dd-b187-4334-b3d3-1d006037e8d7

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange

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
    Submodule.span K (Set.range e) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h := linearIndependent_iff_card_eq_finrank_span.mp he
  rw [Set.finrank] at h
  rw [← h]
  simp
end Formalism.DivisionValues
