-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.CoeffHom.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:30.567403+00:00
-- url     : https://prove2.me/submissions/d7cda92a-9604-4e2e-865a-356811d57e0e

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' : Fin n → ℕ}
    (hP : CoeffHom P μ) (hQ : CoeffHom Q μ') : CoeffHom (P * Q) (μ + μ') := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ fun x _ => (hP x.1).mul (hQ x.2)
end CoeffHom
end Formalism.GradedWeylDivisibility
