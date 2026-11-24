-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.abs_norm_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:47.148315+00:00
-- url     : https://prove2.me/submissions/8573c9b4-4db7-4050-b003-b8e40ed4bee4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution (x : K) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun _ => rfl), ← h2]
  simp
end Formalism.L2.LamCM.A2
