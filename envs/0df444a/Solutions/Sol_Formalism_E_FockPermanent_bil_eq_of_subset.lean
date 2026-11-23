-- Prove2me | solution 1 for Formalism.E.FockPermanent.bil_eq_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:06.324474+00:00
-- url     : https://prove2.me/submissions/1c0d45aa-38b1-4668-b81e-003d44666dab

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
theorem _root_.solution {f g : MvPolynomial τ R} {S : Finset (τ →₀ ℕ)} (h : f.support ⊆ S) :
    bil f g = ∑ m ∈ S, f.coeff m * g.coeff m * (Formalism.A.mfact m : R) :=
  Finset.sum_subset h (fun m _ hm => by
    have : f.coeff m = 0 := by simpa using hm
    simp [this])
end Formalism.E.FockPermanent
