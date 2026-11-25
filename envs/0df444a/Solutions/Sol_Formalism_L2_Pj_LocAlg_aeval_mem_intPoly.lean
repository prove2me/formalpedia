-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.aeval_mem_intPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:09:53.776086+00:00
-- url     : https://prove2.me/submissions/240177ee-da82-4fc4-8c1c-81658e333387

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Theorems.Thm_Formalism_L2_Pj_LocAlg_C_mem_intPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution {σ τ : Type} {W : Subring Ω} {q : σ → MvPolynomial τ Ω}
    (hq : ∀ s, q s ∈ intPoly τ W) {P : MvPolynomial σ Ω} (hP : P ∈ intPoly σ W) :
    aeval q P ∈ intPoly τ W := by
  rw [P.as_sum, map_sum]
  refine Subring.sum_mem _ fun v _ => ?_
  rw [aeval_monomial]
  refine Subring.mul_mem _ ?_ ?_
  · rw [MvPolynomial.algebraMap_eq]
    exact C_mem_intPoly (hP v)
  · exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hq s) _
end Formalism.L2.Pj.LocAlg
