-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.iso_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:59.31682+00:00
-- url     : https://prove2.me/submissions/4830be14-9a7b-49f0-9107-4d7787a23cc3

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_of_integral
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_apply
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_continuous


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
theorem _root_.solution {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {c : ℝ} (hc : c ^ 2 = |B.det|) : Iso ((c : ℂ) • dil B) :=
  iso_of_integral fun f => by
    have hd : LinearMap.det (B : Eu l →ₗ[ℝ] Eu l) ≠ 0 :=
      ((hB.map ContinuousLinearMap.toLinearMapRingHom).map LinearMap.det).ne_zero
    have h1 := integral_map (μ := volume) (φ := (B : Eu l →ₗ[ℝ] Eu l)) (f := fun x => ‖f x‖ ^ (2 : ℝ))
      B.continuous.aemeasurable (f.continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hd, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _)] at h1
    simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, dil_apply hB, norm_smul, norm_real, Real.rpow_two,
      mul_pow, Real.norm_eq_abs, sq_abs, hc, integral_const_mul] at h1 ⊢
    erw [← h1]
    rw [smul_eq_mul, ← mul_assoc, ← abs_mul, ContinuousLinearMap.det, mul_inv_cancel₀ hd, abs_one, one_mul]
end CompanionTheory.ThKR.LL
