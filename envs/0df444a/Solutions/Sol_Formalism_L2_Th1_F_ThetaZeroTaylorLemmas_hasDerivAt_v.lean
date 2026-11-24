-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.hasDerivAt_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:35:12.788254+00:00
-- url     : https://prove2.me/submissions/ef29cd2b-9234-4b6c-b9e1-4d8e65eef422

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_zetaHasDeriv


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
open Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
namespace Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
theorem _root_.solution (L : PeriodPair) {t z : ℂ} (h : z + t ∉ L.lattice) :
    HasDerivAt (v L t) (-(L.weierstrassP (z + t)) - s2 L) z := by
  have h1 : HasDerivAt (fun x => wZeta L (x + t)) (-(L.weierstrassP (z + t))) z :=
    (zetaHasDeriv L (z + t) h).comp_add_const z t
  have h2 : HasDerivAt (fun x : ℂ => s2 L * x) (s2 L * 1) z := (hasDerivAt_id z).const_mul (s2 L)
  rw [mul_one] at h2
  exact (h1.sub_const (wZeta L t)).sub h2
end Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
