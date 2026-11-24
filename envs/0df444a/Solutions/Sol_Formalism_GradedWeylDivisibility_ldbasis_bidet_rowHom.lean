-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldbasis_bidet_rowHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:12.56639+00:00
-- url     : https://prove2.me/submissions/991c2383-2206-4f97-8402-1649bbb44288

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_initMinor_rowHom
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    IsWeightedHomogeneous (rowW r n) (bideterminant R sz hsz I)
      (∑ k : Fin K, ∑ p : Fin (sz k), Pi.single (I k p) 1) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ (fun k _ => ldbasis_initMinor_rowHom R (I k) (hsz k))
end Formalism.GradedWeylDivisibility
