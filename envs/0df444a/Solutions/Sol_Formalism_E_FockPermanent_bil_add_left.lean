-- Prove2me | solution 1 for Formalism.E.FockPermanent.bil_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:21.940865+00:00
-- url     : https://prove2.me/submissions/24bcd1a2-c482-4eca-a7c8-1be3929062c2

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm
import Theorems.Thm_Formalism_E_FockPermanent_bil_eq_of_subset

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
theorem _root_.solution (f f' g : MvPolynomial τ R) : bil (f + f') g = bil f g + bil f' g := by
  classical
  rw [bil_eq_of_subset (S := f.support ∪ f'.support) support_add,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_left,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_right, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring
end Formalism.E.FockPermanent
