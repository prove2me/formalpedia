-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_odd_characteristic_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/6c96b16e-efdf-46cf-b5df-9ecc929d3008

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_encoded_kQuotient_of_odd

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution :
    ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j)) := by
  intro f hf j _
  exact symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (GaloisField 3 j)
    ((CharP.cast_eq_zero_iff (GaloisField 3 j) 3 2).not.mpr (by norm_num)) hf
end CompactnessConjecture
