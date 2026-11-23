-- Prove2me | solution 1 for Formalism.CyclotomicNorms.SubstitutionExponents.revLex_wf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:51.59467+00:00
-- url     : https://prove2.me/submissions/22dd904b-9ad5-4aa2-b93e-241ab3de1719

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.SubstitutionExponents
variable {r : ℕ}
namespace Formalism.CyclotomicNorms.SubstitutionExponents
theorem _root_.solution : WellFounded (revLex (r := r)) :=
  Finsupp.Lex.wellFounded_of_finite _ wellFounded_lt
end Formalism.CyclotomicNorms.SubstitutionExponents
