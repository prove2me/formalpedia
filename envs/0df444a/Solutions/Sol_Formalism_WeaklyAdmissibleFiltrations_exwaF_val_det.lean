-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_val_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:27.393825+00:00
-- url     : https://prove2.me/submissions/d8fc8493-0d08-45af-b890-9b4fcadabc6f

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaPhi_pow_n
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_val_det
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (v : AddValuation LL (WithTop ℚ)) (c : LL) (hc : c ≠ 0) (r : ℚ)
    (hr : v c = (r : WithTop ℚ)) :
    v (LinearMap.det ((exwaF (n := n) c hc).φ : (ZMod n → LL) →ₗ[LL] (ZMod n → LL))) =
      (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
  have hcn : v (c ^ n) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]
  exact exwa_val_det v _ n (NeZero.ne n) exwa_finrank (c ^ n) _ (exwaPhi_pow_n c hc) hcn
end Formalism.WeaklyAdmissibleFiltrations
