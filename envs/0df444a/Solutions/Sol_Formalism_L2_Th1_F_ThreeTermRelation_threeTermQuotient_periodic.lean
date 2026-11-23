-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:46.727212+00:00
-- url     : https://prove2.me/submissions/6c3f0735-99e3-473a-8445-dcd40cc1de6a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_semiChar_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThreeTermRelation
variable (L : PeriodPair) (b c : ℂ)
namespace Formalism.L2.Th1.F.ThreeTermRelation
theorem _root_.solution (hq : SigmaQuasi) : IsPeriodic L (threeTermQuotient L b c) := by
  intro ω hω x
  have h0 := hq L ω x hω
  have h1 : wSigma L (x + ω + (b + c))
      = semiChar L ω * Complex.exp (wEta L ω * (x + (b + c) + ω / 2)) * wSigma L (x + (b + c)) := by
    rw [← hq L ω (x + (b + c)) hω]; congr 1; ring
  have h2 : wSigma L (x + ω + -b)
      = semiChar L ω * Complex.exp (wEta L ω * (x + -b + ω / 2)) * wSigma L (x + -b) := by
    rw [← hq L ω (x + -b) hω]; congr 1; ring
  have h3 : wSigma L (x + ω + -c)
      = semiChar L ω * Complex.exp (wEta L ω * (x + -c + ω / 2)) * wSigma L (x + -c) := by
    rw [← hq L ω (x + -c) hω]; congr 1; ring
  have hP : L.weierstrassP (x + ω) = L.weierstrassP x := L.weierstrassP_add_coe x ⟨ω, hω⟩
  have hP' : L.derivWeierstrassP (x + ω) = L.derivWeierstrassP x :=
    L.derivWeierstrassP_add_coe x ⟨ω, hω⟩
  have hE : Complex.exp (wEta L ω * (x + (b + c) + ω / 2)) * Complex.exp (wEta L ω * (x + -b + ω / 2))
        * Complex.exp (wEta L ω * (x + -c + ω / 2))
      = Complex.exp (wEta L ω * (x + ω / 2)) ^ 3 := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hχ : semiChar L ω ≠ 0 := fun h => by simpa [h] using semiChar_mul_self L ω
  have hne : semiChar L ω ^ 3 * Complex.exp (wEta L ω * (x + ω / 2)) ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hχ) (pow_ne_zero _ (Complex.exp_ne_zero _))
  unfold threeTermQuotient nAux threeTermDenom threeTermDet
  rw [h0, h1, h2, h3, hP, hP']
  rw [← mul_div_mul_left _ (wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)) hne]
  congr 1
  · ring
  · rw [← hE]; ring
end Formalism.L2.Th1.F.ThreeTermRelation
