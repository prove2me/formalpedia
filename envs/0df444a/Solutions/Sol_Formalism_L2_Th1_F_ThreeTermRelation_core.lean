-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:19.524261+00:00
-- url     : https://prove2.me/submissions/5ff80993-1bff-4b50-b7e2-cef3e8b4c434

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_eq_of_eventuallyEq_punctured
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_eq_twistedGamma_of_sigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_twistedGamma_zero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_twistedGamma_analyticAt_zero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_mem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_notMem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermDenom_eventually_ne
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermDenom_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_meromorphicAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_periodic
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_off
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_lattice

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
theorem _root_.solution (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice)
    (hm : b - c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  obtain ⟨k, hk⟩ := h1 L (threeTermQuotient L b c) (-(b + c)) (threeTermQuotient_meromorphicAt L b c he)
    (threeTermQuotient_periodic L b c hq)
    (fun z hzp => by
      by_cases hzL : z ∈ L.lattice
      · exact threeTermQuotient_order_lattice L b c he hz hord hq hb hc hp hzL
      · have := threeTermQuotient_order_off L b c he hord hm hzL
          (sig_order_notMem L hord (β := b + c) (by rwa [sub_neg_eq_add] at hzp))
        simpa using this)
    (by
      have hpL : -(b + c) ∉ L.lattice := fun h => hp (by simpa using L.lattice.neg_mem h)
      have := threeTermQuotient_order_off L b c he hord hm hpL
        (sig_order_mem L hord (β := b + c) (by simp))
      simpa using this)
  have hev : ∀ z, ∀ᶠ x in 𝓝[≠] z, nAux L b c x = k * threeTermDenom L b c x := by
    intro z
    filter_upwards [eventually_notMem L z, threeTermDenom_eventually_ne L b c he hord z] with x hx1 hx2
    have := hk x ((threeTermNum_analyticAt L b c he x hx1).div (threeTermDenom_analyticAt L b c he x) hx2).continuousAt
    unfold threeTermQuotient at this
    rw [div_eq_iff hx2] at this
    exact this
  have hmc : ∀ z, ContinuousAt (fun x => k * threeTermDenom L b c x) z := fun z =>
    continuousAt_const.mul (threeTermDenom_analyticAt L b c he z).continuousAt
  have h0 : frobeniusStickelbergerDetMulSigmaCube L b c 0 = k * threeTermDenom L b c 0 := by
    refine eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (twistedGamma_analyticAt_zero L b c he).continuousAt (hmc 0) ?_
    filter_upwards [hev 0, self_mem_nhdsWithin] with x hx1 hx2
    rw [← threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx2, hx1]
  have ha' : nAux L b c a = k * threeTermDenom L b c a :=
    eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (threeTermNum_analyticAt L b c he a ha).continuousAt (hmc a) (hev a)
  have hS : wSigma L (b + c) ≠ 0 := fun h => hp ((hz L _).1 h)
  have h3 := hadd L b c hb hc
  rw [twistedGamma_zero L b c hz hs] at h0
  unfold threeTermDenom at h0 ha'
  unfold nAux at ha'
  rw [zero_add, zero_add, zero_add, ho L b, ho L c] at h0
  have e1 : a + (b + c) = a + b + c := by ring
  have e2 : a + -b = a - b := by ring
  have e3 : wSigma L (a + -c) = -wSigma L (c - a) := by rw [← ho L]; congr 1; ring
  rw [e1, e2, e3] at ha'
  refine mul_left_cancel₀ hS ?_
  linear_combination (wSigma L (b + c) * wSigma L b ^ 3 * wSigma L c ^ 3) * ha'
    + (wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a) * wSigma L b ^ 2 * wSigma L c ^ 2) * h0
    - (2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a)) * h3
end Formalism.L2.Th1.F.ThreeTermRelation
