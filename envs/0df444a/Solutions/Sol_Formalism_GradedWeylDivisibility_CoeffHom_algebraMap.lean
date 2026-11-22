-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.CoeffHom.algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:24:43.285113+00:00
-- url     : https://prove2.me/submissions/a3b2e70a-c1ce-4eaa-9e44-005b2e0148c8

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable

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
namespace CoeffHom
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    CoeffHom (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs
  · rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  · exact isWeightedHomogeneous_zero R _ _
end CoeffHom
end Formalism.GradedWeylDivisibility
