-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.rho_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:13.64301+00:00
-- url     : https://prove2.me/submissions/4067c6cb-d3ce-41da-ad81-22c37997288a

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
theorem _root_.solution (c : ℝ) (w : ι → Fin r → ℂ) : rho eqv ((c : ℂ) • w) = c • rho eqv w := by
  funext k
  simp only [rho, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp
end Formalism.L2.Pj.FundamentalDomainD5
