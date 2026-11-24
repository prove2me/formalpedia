-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.rho_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:12.710411+00:00
-- url     : https://prove2.me/submissions/221edf73-36ac-4374-8ce9-15a5a1b03b1d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_add
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_zero

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
theorem _root_.solution {κ : Type} (s : Finset κ) (w : κ → ι → Fin r → ℂ) :
    rho eqv (∑ j ∈ s, w j) = ∑ j ∈ s, rho eqv (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rho_add, ih]
end Formalism.L2.Pj.FundamentalDomainD5
