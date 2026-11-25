-- Prove2me | solution 1 for ChromaticReconstruction.card_eq_of_chromSymm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:30:35.004025+00:00
-- url     : https://prove2.me/submissions/9ba7477b-0dd7-465c-84df-47927878d620

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
import Theorems.Thm_ChromaticReconstruction_coeff_chromSymm_replicate_one


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {G : SimpleGraph V} {H : SimpleGraph W}
    (h : chromSymm G = chromSymm H) : Fintype.card V = Fintype.card W := by
  have h1 := coeff_chromSymm_replicate_one G (Fintype.card V)
  rw [h, coeff_chromSymm_replicate_one] at h1
  by_contra hne
  rw [if_neg hne, if_pos rfl] at h1
  exact zero_ne_one h1
end ChromaticReconstruction
