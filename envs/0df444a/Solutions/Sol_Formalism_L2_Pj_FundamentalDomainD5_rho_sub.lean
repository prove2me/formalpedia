-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.rho_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:38.011983+00:00
-- url     : https://prove2.me/submissions/23ca416f-9b0a-4d78-9ee9-939daac6af1b

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
theorem _root_.solution (w w' : ι → Fin r → ℂ) : rho eqv (w - w') = rho eqv w - rho eqv w' := by
  funext k
  simp only [rho, Pi.sub_apply]
  split_ifs <;> simp
end Formalism.L2.Pj.FundamentalDomainD5
