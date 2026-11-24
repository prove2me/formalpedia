-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:44.86173+00:00
-- url     : https://prove2.me/submissions/c2c2fa18-efb2-41f2-8c33-feae03e1b517

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_rowDiv_map
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
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord S w (map φ f) = map φ (applyWord R w f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih, lclosedeq_rowDiv_map]
end Formalism.GradedWeylDivisibility
