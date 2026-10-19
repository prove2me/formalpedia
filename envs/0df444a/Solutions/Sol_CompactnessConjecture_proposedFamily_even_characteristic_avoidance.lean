-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_even_characteristic_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/fc3a42ae-a63d-4a37-8fc3-26257d76c9bf

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_encoded_jQuotient_of_char_two

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution :
    ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)) :=
  fun _ hf j _ =>
    symplecticQuadrangle_no_encoded_jQuotient_of_char_two
      (GaloisField 2 j) hf
end CompactnessConjecture
