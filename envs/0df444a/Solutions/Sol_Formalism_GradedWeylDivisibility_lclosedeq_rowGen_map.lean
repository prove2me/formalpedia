-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lclosedeq_rowGen_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:15.001931+00:00
-- url     : https://prove2.me/submissions/8e6e3868-adae-4384-aadc-e5d863ab2b50

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
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
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [map_C, rowGen, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq, Polynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p v hp =>
    simp only [map_mul, map_X, hp, Polynomial.map_mul]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp [Polynomial.map_add, Polynomial.map_mul, map_X]
end Formalism.GradedWeylDivisibility
