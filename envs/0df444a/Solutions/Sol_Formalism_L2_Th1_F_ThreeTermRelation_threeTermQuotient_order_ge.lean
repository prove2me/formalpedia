-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:46.683581+00:00
-- url     : https://prove2.me/submissions/fa8e2529-5201-4ca9-9307-484876c347f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_le_sub_of_add_le
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermDenom_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_meromorphicAt

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
theorem _root_.solution (he : SigmaEntire) {z : ℂ} {k m1 m2 m3 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ))
    (h2 : meromorphicOrderAt (fun w => wSigma L (w + -b)) z = (m2 : WithTop ℤ))
    (h3 : meromorphicOrderAt (fun w => wSigma L (w + -c)) z = (m3 : WithTop ℤ))
    (hN : ((k + (m1 + m2 + m3) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (nAux L b c) z) :
    (k : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have hm : meromorphicOrderAt (threeTermDenom L b c) z = ((m1 + m2 + m3 : ℤ) : WithTop ℤ) := by
    have e : threeTermDenom L b c = ((fun w => wSigma L (w + (b + c))) * (fun w => wSigma L (w + -b)))
        * (fun w => wSigma L (w + -c)) := rfl
    rw [e, meromorphicOrderAt_mul ((sig_analyticAt L he (b + c) z).mul
        (sig_analyticAt L he (-b) z)).meromorphicAt (sig_analyticAt L he (-c) z).meromorphicAt,
      meromorphicOrderAt_mul (sig_analyticAt L he (b + c) z).meromorphicAt
        (sig_analyticAt L he (-b) z).meromorphicAt, h1, h2, h3]
    rfl
  unfold threeTermQuotient
  rw [fun_meromorphicOrderAt_div (threeTermNum_meromorphicAt L b c he z)
    (threeTermDenom_analyticAt L b c he z).meromorphicAt, hm]
  exact le_sub_of_add_le hN
end Formalism.L2.Th1.F.ThreeTermRelation
