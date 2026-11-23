-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.norm_exp_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:17.193423+00:00
-- url     : https://prove2.me/submissions/955081bd-202f-4edb-95e2-ae51ad8c83de

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe

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
theorem _root_.solution (a b : ℝ) : ‖exp ((a : ℂ) * I) - exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have : exp ((a : ℂ) * I) - exp ((b : ℂ) * I) = exp ((b : ℂ) * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le
end CompanionTheory.ThKR.LL
