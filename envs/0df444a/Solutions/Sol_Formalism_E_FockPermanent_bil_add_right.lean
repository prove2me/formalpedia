-- Prove2me | solution 1 for Formalism.E.FockPermanent.bil_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:21.854802+00:00
-- url     : https://prove2.me/submissions/570f325f-00e6-4363-92ae-41617eefac67

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
open Formalism Formalism.E
open Formalism.E.FockPermanent
variable {R τ : Type*} [CommRing R]
namespace Formalism.E.FockPermanent
theorem _root_.solution (f g g' : MvPolynomial τ R) : bil f (g + g') = bil f g + bil f g' := by
  rw [bil, bil, bil, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring
end Formalism.E.FockPermanent
