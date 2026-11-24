-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crRho_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:42.916614+00:00
-- url     : https://prove2.me/submissions/a3454a6c-2b1c-4c4f-9195-b64fcb50eea8

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crX_mem
import Theorems.Thm_Formalism_L2_Pj_Crude_crRho_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (p : MvPolynomial (Letter T r n) R) : crRho R β p ∈ supported R (crDiag β) := by
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro u c
    rw [crRho_monomial]
    split_ifs with h
    · rw [monomial_eq, ← MvPolynomial.algebraMap_eq]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
        (Subalgebra.prod_mem _ fun ℓ hℓ => Subalgebra.pow_mem _ (crX_mem (h ℓ hℓ)) _)
    · exact Subalgebra.zero_mem _
  · intro p q hp hq
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq
end Formalism.L2.Pj.Crude
