-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.rho_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:59.79836+00:00
-- url     : https://prove2.me/submissions/b009cd15-5fd2-453f-ae9f-ffeac58125a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open Matrix ComplexConjugate
variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution (w w' : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w' = ∑ i, ∑ a, (conj (w i a) * w' i a).re := by
  unfold dotProduct
  rw [← eqv.symm.sum_comp]
  simp only [rho, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Complex.mul_re]
end Formalism.L2.Pj.FundamentalDomainD5
