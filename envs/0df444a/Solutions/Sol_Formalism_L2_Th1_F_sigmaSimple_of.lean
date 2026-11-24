-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaSimple_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:44.967838+00:00
-- url     : https://prove2.me/submissions/a994aeaa-81bf-471c-a607-c0420649ca57

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_semiChar_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution (hq : SigmaQuasi) (he : SigmaEntire)
    (h0 : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1) : SigmaSimple := by
  intro L
  refine ⟨h0 L, fun z hzL => ?_⟩
  have h : HasDerivAt (fun y => wSigma L (y + z)) (deriv (wSigma L) z) 0 := by
    have h' := (he L (0 + z)).hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id' (0 : ℂ)).add_const z)
    rw [zero_add, mul_one] at h'
    exact h'
  have hd1 : HasDerivAt (fun y => semiChar L z * Complex.exp (wEta L z * (y + z / 2))
      * wSigma L y) (deriv (wSigma L) z) 0 := by
    convert h using 1
    funext y
    exact (hq L z y hzL).symm
  have h3 : HasDerivAt (fun y => Complex.exp (wEta L z * (y + z / 2)))
      (Complex.exp (wEta L z * (0 + z / 2)) * (wEta L z * 1)) 0 :=
    (((hasDerivAt_id' (0 : ℂ)).add_const (z / 2)).const_mul (wEta L z)).cexp
  have hd2 := (h3.const_mul (semiChar L z)).mul (he L 0).hasDerivAt
  have hσ0 : wSigma L 0 = 0 := by simp [wSigma]
  rw [hd1.unique hd2, hσ0, h0 L]
  simp [Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.semiChar_ne_zero, Complex.exp_ne_zero]
end Formalism.L2.Th1.F
