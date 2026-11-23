-- Prove2me | solution 1 for Formalism.E.fock_eq_sum_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:26.139533+00:00
-- url     : https://prove2.me/submissions/0c80be3e-0d88-4f31-a4a6-4befa578d4d0

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockSesq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MvPolynomial
open Formalism Formalism.E
variable {R τ : Type*} [CommRing R] [StarRing R]
namespace Formalism.E
theorem _root_.solution (f g : MvPolynomial τ R) (s : Finset (τ →₀ ℕ))
    (h : f.support ⊆ s) :
    fock f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R) := by
  classical
  unfold fock
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]
end Formalism.E
