-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.CoeffHom.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:12.322531+00:00
-- url     : https://prove2.me/submissions/f9cee3c3-e008-48cc-b288-59a7785ce9e2

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} :
    CoeffHom (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one R _
  · exact isWeightedHomogeneous_zero R _ _
end CoeffHom
end Formalism.GradedWeylDivisibility
