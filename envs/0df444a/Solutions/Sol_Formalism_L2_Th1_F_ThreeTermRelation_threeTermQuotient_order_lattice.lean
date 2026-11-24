-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:45.587234+00:00
-- url     : https://prove2.me/submissions/2c0eab88-7b19-4e7e-a424-003be19debda

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_periodic
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_zero

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
theorem _root_.solution (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder) (hq : SigmaQuasi)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) {z : ℂ}
    (hzL : z ∈ L.lattice) : 0 ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have h := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := 0) (c := z)
    (f := threeTermQuotient L b c)
  have h' : threeTermQuotient L b c ∘ (· + z) = threeTermQuotient L b c := funext fun x => threeTermQuotient_periodic L b c hq z hzL x
  rw [h', zero_add] at h
  rw [← h]
  exact threeTermQuotient_order_zero L b c he hz hord hb hc hp
end Formalism.L2.Th1.F.ThreeTermRelation
