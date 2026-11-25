-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_linF_pow_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:13.601967+00:00
-- url     : https://prove2.me/submissions/80be32c4-4334-4f7c-bfa7-ddcee7bf130e

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_linF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {τ : Type} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (lam : τ → K) (w : τ) (m : τ →₀ ℕ) (k : ℕ) :
    coeff (m + Finsupp.single w 1) (linF lam ^ (k + 1)) * ((m w : K) + 1)
      = ((k : K) + 1) * lam w * coeff m (linF lam ^ k) := by
  have h := congrArg (coeff m) (Derivation.leibniz_pow (pderiv K w) (linF lam) (k + 1))
  rw [coeff_pderiv, pderiv_linF] at h
  rw [h]
  rw [Nat.add_sub_cancel, smul_eq_mul, map_nsmul, MvPowerSeries.coeff_mul_C, nsmul_eq_mul]
  push_cast
  ring
end Formalism.L2.FormalSeriesBounds
