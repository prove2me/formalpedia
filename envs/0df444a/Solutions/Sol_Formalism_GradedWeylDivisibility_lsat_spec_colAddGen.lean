-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lsat_spec_colAddGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:10.379+00:00
-- url     : https://prove2.me/submissions/7a418e1b-ef47-4b8b-b220-db7bbd48b859

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LSatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylPoint

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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp (colAddGen R l j) =
      colAdd R l j c := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp
end Formalism.GradedWeylDivisibility
