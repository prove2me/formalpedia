-- Prove2me | solution 1 for Formalism.QuantumDeterminants.length_additive_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:55.188032+00:00
-- url     : https://prove2.me/submissions/5fda55c4-23fb-41ab-88b0-232d0450fb88

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_ell_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open WeylGroupFacts
namespace Formalism.QuantumDeterminants
theorem _root_.solution : EllAdd := by
  unfold EllAdd
  intro k r z hz g hg h hh
  exact ell_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2
end Formalism.QuantumDeterminants
