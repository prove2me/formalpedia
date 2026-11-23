-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ndEv_colAddGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:09.841189+00:00
-- url     : https://prove2.me/submissions/12a9e122-5ce4-45c4-8905-b59977d21327

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom

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
    ndEv R r n (colAddGen R l j g) = g := by
  have : (ndEv R r n).comp (colAddGen R (r := r) l j) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, colAddGen, aeval_X, AlgHom.id_apply]
    split_ifs <;> simp [ndEv]
  exact congrArg (fun φ => φ g) this
end Formalism.GradedWeylDivisibility
