-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaDouble_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:12.089736+00:00
-- url     : https://prove2.me/submissions/86a956ff-4eef-479c-ba41-3aecbb703263

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_PDeriv
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_eventually_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PDeriv
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : SigmaAdd) (he : SigmaEntire) (hs : SigmaSimple) : SigmaDouble := by
  intro L z hz
  have h0 : wSigma L 0 = 0 := by simp only [wSigma, zero_mul]
  have hd : ∀ x, HasDerivAt (wSigma L) (deriv (wSigma L) x) x := fun x => (he L x).hasDerivAt
  have hF := (HasDerivAt.comp z (hd (z + z)) ((hasDerivAt_id' z).const_add z)).mul
    (HasDerivAt.comp z (hd (z - z)) ((hasDerivAt_id' z).const_sub z))
  have hG := ((((hd z).mul (hd z)).const_mul (wSigma L z ^ 2)).mul
    ((hasDerivAt_P L hz).const_sub (L.weierstrassP z))).neg
  have hG' : HasDerivAt (fun w => wSigma L (z + w) * wSigma L (z - w)) _ z :=
    hG.congr_of_eventuallyEq ((eventually_notMem L hz).mono fun w hw => by
      simp only [Pi.neg_apply, Pi.mul_apply]
      rw [h L z w hz hw]
      ring)
  have key := hF.unique hG'
  simp only [Function.comp_apply, Pi.mul_apply, sub_self, h0, (hs L).1] at key
  rw [two_mul]
  linear_combination -key
end Formalism.L2.Th1.F
