-- Prove2me | solution 1 for Formalism.ELL.unitAtAlt.of_model
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:44.16443+00:00
-- url     : https://prove2.me/submissions/9401f323-1f86-48cf-b497-d77cace09fe2

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ModelUnitOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.ELL Formalism.ELL.unitAtAlt
open Formalism.ELL
namespace Formalism.ELL.unitAtAlt
theorem _root_.solution {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by
  have hne : W.Δ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΔ; exact zero_ne_one hΔ
  have : W.IsElliptic := ⟨hne.isUnit⟩
  refine ⟨W, inferInstance, hI, hΔ, ?_⟩
  rw [WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp
end Formalism.ELL.unitAtAlt
