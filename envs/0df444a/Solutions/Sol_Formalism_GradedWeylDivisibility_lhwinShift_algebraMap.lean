-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwinShift_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:55.762869+00:00
-- url     : https://prove2.me/submissions/f598adf8-79f5-4eeb-9dfd-635c26e022a9

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (c : R) (δ : ℤ) :
    LhwinShift (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (lhwinHt r n) c
  · exact isWeightedHomogeneous_zero R _ _
end Formalism.GradedWeylDivisibility
