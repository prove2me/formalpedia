-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_val_det_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:28.342895+00:00
-- url     : https://prove2.me/submissions/6baf7b6e-12d1-430c-b6bc-7007a29009e3

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaPhi_pow_n
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_val_det
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_restrict_pow_coe
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
    (hr : v c = (r : WithTop ℚ)) (h : ∀ x ∈ (⊤ : Submodule LL (ZMod n → LL)),
      (exwaF (n := n) c hc).φ x ∈ (⊤ : Submodule LL (ZMod n → LL))) :
    v (LinearMap.det ((exwaF (n := n) c hc).φres ⊤ h)) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
  have hcn : v (c ^ n) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]
  refine exwa_val_det v _ n (NeZero.ne n) (by rw [finrank_top, exwa_finrank]) (c ^ n) _ ?_ hcn
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [FilPhi.φres, exwa_restrict_pow_coe]
  change ((exwaPhi (n := n) c hc).toLinearMap ^ n) (x : ZMod n → LL) = _
  rw [exwaPhi_pow_n]
  simp
end Formalism.WeaklyAdmissibleFiltrations
