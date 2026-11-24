-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lclosedeq_rowDiv_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:50.342842+00:00
-- url     : https://prove2.me/submissions/78960977-c333-448c-ab2d-a11913704371

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_rowGen_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv S a b k (map φ f) = map φ (rowDiv R a b k f) := by
  simp only [rowDiv, lclosedeq_rowGen_map, Polynomial.coeff_map]
end Formalism.GradedWeylDivisibility
