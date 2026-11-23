-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.intw_fou
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:47.547365+00:00
-- url     : https://prove2.me/submissions/93bae3d8-a229-4666-95f9-5b971589e292

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_fou_apply

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
theorem _root_.solution (p q : Eu l) : Intw (fou l) p q (-q) p := fun f g h => by
  funext x
  simp only [fou_apply, fourier_coe, rf, h, Real.fourier_eq', smul_eq_mul]
  rw [← integral_const_mul, ← integral_add_right_eq_self (μ := volume) (fun v => exp (((2 * π * ⟪p, x⟫ + π * ⟪-q, p⟫ : ℝ) : ℂ) * I) *
    (exp (((-2 * π * ⟪v, x + -q⟫ : ℝ) : ℂ) * I) * f v)) p]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, real_inner_comm q p, real_inner_comm q v]
  ring
end CompanionTheory.ThKR.LL
