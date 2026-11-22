-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.CoeffHom.gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:41.091477+00:00
-- url     : https://prove2.me/submissions/e4a2d591-428e-48a8-801e-886145e846b2

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    CoeffHom (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (colW r n v) := by
  intro k
  have hX : IsWeightedHomogeneous (colW r n) (X v : MvPolynomial (Fin r × Fin n) R) (colW r n v) :=
    isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (colW r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (colW r n v) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs
      · exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _
end CoeffHom
end Formalism.GradedWeylDivisibility
