-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.rho_dot_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:11.881906+00:00
-- url     : https://prove2.me/submissions/76e1b6f8-a623-4a98-90c9-431d8e2f35c1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_dot

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
theorem _root_.solution (w : ι → Fin r → ℂ) : rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ a, ‖w i a‖ ^ 2 := by
  rw [rho_dot]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring
end Formalism.L2.Pj.FundamentalDomainD5
