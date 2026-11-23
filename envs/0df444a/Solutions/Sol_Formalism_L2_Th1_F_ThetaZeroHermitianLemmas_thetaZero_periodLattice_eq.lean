-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.thetaZero_periodLattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:36.956808+00:00
-- url     : https://prove2.me/submissions/6b7ad440-22f9-4246-8012-8406036cbd34

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_zero_left

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
open Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
namespace Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
theorem _root_.solution (L : PeriodPair) (t z : ℂ) :
    th0 L t z = sgStar L (z + t) * Complex.exp (-(Real.pi : ℂ) * herm L z t) / sgStar L t := by
  have h1 : Complex.exp (-(Real.pi : ℂ) * herm L z t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-(Real.pi : ℂ) * herm L z t) * Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [← Complex.exp_add]; congr 1
  have h2 : Complex.exp (-(Real.pi : ℂ) * herm L 0 t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [herm_zero_left]; congr 1; ring
  simp only [th0, opU, zero_add, h1, h2]
  rw [← mul_assoc, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
end Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
