-- Prove2me | solution 1 for Formalism.L2.Th1.F.th0Class_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:46.487802+00:00
-- url     : https://prove2.me/submissions/c825df8f-aaaa-4130-b70a-f0f16e6db5d9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_add_left
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_add_right
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_thetaZero_periodLattice_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ThetaZeroHermitianLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution (hb : SgStarBasic) (hq : SgStarQuasi) : ThetaZeroClass := by
  intro L t ω z hω ht
  have hs : sgStar L t ≠ 0 := fun h0 => ht (((hb L).2.2.1 t).1 h0)
  have hc : semiChar L ω ≠ 0 := by unfold semiChar; split_ifs <;> norm_num
  have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * herm L z (t + ω))
      = Complex.exp (-(Real.pi : ℂ) * herm L z t)
        * Complex.exp ((Real.pi : ℂ) * herm L t ω + (Real.pi : ℂ) * herm L ω ω / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    rw [herm_add_left, herm_add_right]; ring
  rw [thetaZero_periodLattice_eq L (t + ω) z, thetaZero_periodLattice_eq L t z, ← add_assoc, hq L ω (z + t) hω, hq L ω t hω,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) hs) hs]
  linear_combination (semiChar L ω * sgStar L (z + t) * sgStar L t) * key
end Formalism.L2.Th1.F
