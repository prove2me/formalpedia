-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.ld_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:08.381521+00:00
-- url     : https://prove2.me/submissions/f7a78495-de7c-48de-b35e-d8c5c9a60711

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Theorems.Thm_CompanionTheory_ThKR_LL_ld_dil_one
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution {B : ℝ → Eu l →L[ℝ] Eu l} {B' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt B B' t₀) (h0 : IsUnit (B t₀)) :
    LD (fun t => dil (B t)) (fun f => vf (Ring.inverse (B t₀) * B') (dil (B t₀) f)) t₀ := fun f => by
  refine ld_dil_one (h.const_mul (Ring.inverse (B t₀))) (Ring.inverse_mul_cancel _ h0) _ ?_
  filter_upwards [h.continuousAt.eventually (Units.isOpen.mem_nhds h0)] with t ht x
  rw [dil_apply ht, dil_apply h0, ← ContinuousLinearMap.mul_apply, ← mul_assoc, Ring.mul_inverse_cancel _ h0, one_mul]
end CompanionTheory.ThKR.LL
