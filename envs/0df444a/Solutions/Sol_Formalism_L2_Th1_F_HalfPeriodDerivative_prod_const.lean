-- Prove2me | solution 1 for Formalism.L2.Th1.F.HalfPeriodDerivative.prod_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:35.652479+00:00
-- url     : https://prove2.me/submissions/145effe4-1bfc-4ef5-b1f0-ebb1f7a5919c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.HalfPeriodDerivative
namespace Formalism.L2.Th1.F.HalfPeriodDerivative
theorem _root_.solution (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (L : PeriodPair) {t z : ℂ}
    (ht : t ∉ L.lattice) (h2 : 2 * t ∈ L.lattice) (hzL : z ∉ L.lattice) (hzt : z + t ∉ L.lattice) :
    (L.weierstrassP (z + t) - L.weierstrassP t) * (L.weierstrassP z - L.weierstrassP t)
      * wSigma L t ^ 4 = Complex.exp (wEta L (2 * t) * t) := by
  have a1 := ha L (z + t) t hzt ht
  have a2 := ha L z t hzL ht
  have q1 := hq L (2 * t) z h2
  have q2 := hq L (2 * t) (z - t) h2
  have e1 : z + t + t = z + 2 * t := by ring
  have e2 : z + t - t = z := by ring
  have e3 : z - t + 2 * t = z + t := by ring
  have e4 : z + 2 * t / 2 = z + t := by ring
  have e5 : z - t + 2 * t / 2 = z := by ring
  rw [e1, e2] at a1
  rw [e4] at q1
  rw [e3, e5] at q2
  have hs1 : wSigma L z ≠ 0 := mt (hz L z).1 hzL
  have hs2 : wSigma L (z + t) ≠ 0 := mt (hz L (z + t)).1 hzt
  have hE : Complex.exp (wEta L (2 * t) * (z + t))
      = Complex.exp (wEta L (2 * t) * z) * Complex.exp (wEta L (2 * t) * t) := by
    rw [← Complex.exp_add, mul_add]
  have hK : wSigma L (z + t) ^ 2 * wSigma L z ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hs2) (pow_ne_zero _ hs1)
  apply mul_right_cancel₀ hK
  linear_combination (wSigma L z ^ 2 * wSigma L t ^ 2 * (L.weierstrassP z - L.weierstrassP t)) * a1
    - (wSigma L (z + 2 * t) * wSigma L z) * a2
    + (wSigma L z * wSigma L (z + t)) * (wSigma L (z - t) * q1
      - Complex.exp (wEta L (2 * t) * t) * wSigma L z * q2
      + semiChar L (2 * t) * wSigma L z * wSigma L (z - t) * hE)
end Formalism.L2.Th1.F.HalfPeriodDerivative
