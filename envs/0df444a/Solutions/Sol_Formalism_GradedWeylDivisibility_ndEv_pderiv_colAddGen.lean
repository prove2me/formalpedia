-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ndEv_pderiv_colAddGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:00.297189+00:00
-- url     : https://prove2.me/submissions/b0bd203f-f94a-4672-b190-8bf843a31aad

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEv_colAddGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (pderiv none (colAddGen R l j g)) = ndE R r n l j g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [colAddGen, derivation_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, hp, ndEv_colAddGen, ndEv_colAddGen, smul_eq_mul, smul_eq_mul]
    congr 1
    simp only [ndE, mkDerivation_X, colAddGen, aeval_X]
    split_ifs <;> simp [ndEv, Derivation.leibniz, pderiv_X]
end Formalism.GradedWeylDivisibility
