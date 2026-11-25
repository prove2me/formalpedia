-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.coeff_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:56.6693+00:00
-- url     : https://prove2.me/submissions/da1ac716-f18b-4f5e-b6b9-7ba5fa5a552d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan

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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (lam : K →ₗ[ℚ] ℚ) (P : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (comp lam P) = lam (coeff m P) := by
  by_cases h : coeff m P = 0 <;> simp [comp, coeff_sum, coeff_monomial, h]
end Formalism.L2.FormalSeriesBounds.HaP
