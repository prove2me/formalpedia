-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionNumerator_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:19:24.607798+00:00
-- url     : https://prove2.me/submissions/7a23059b-0a39-4efd-a929-023bc25347b7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionNumerator_neg
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_twistedGamma_analyticAt_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_twistedGamma_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
namespace Formalism.L2.Th1.F
namespace SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
private lemma exists_twistedGamma_eq_sq_mul_analytic (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    ∃ m : ℂ → ℂ, AnalyticAt ℂ m 0 ∧ ∀ y, frobeniusStickelbergerDetMulSigmaCube L w y = y ^ 2 * m y := by
  have hg0 := twistedGamma_zero L w ho hz hs

  have hder : deriv (frobeniusStickelbergerDetMulSigmaCube L w) 0 = 0 := by
    have h1 : deriv (fun y => frobeniusStickelbergerDetMulSigmaCube L w (-y)) 0 = -deriv (frobeniusStickelbergerDetMulSigmaCube L w) (-0) :=
      deriv_comp_neg (f := frobeniusStickelbergerDetMulSigmaCube L w) (x := 0)
    have h2 : (fun y => frobeniusStickelbergerDetMulSigmaCube L w (-y)) = frobeniusStickelbergerDetMulSigmaCube L w := funext (additionNumerator_neg L w ho)
    rw [h2, neg_zero] at h1
    linear_combination h1 / 2
  obtain ⟨p, hp⟩ := twistedGamma_analyticAt_zero L w he
  have hm := hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope
  refine ⟨dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0, ⟨_, hm⟩, fun y => ?_⟩
  have e1 := sub_smul_dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0 y
  have e2 := sub_smul_dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0 y
  rw [dslope_same, hder] at e2
  simp only [sub_zero, smul_eq_mul, hg0] at e1 e2
  rw [← e1, ← e2]
  ring
end SigmaAdditionFormula
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
namespace Formalism.L2.Th1.F.SigmaAdditionFormula
theorem _root_.solution (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    (2 : WithTop ℤ) ≤ meromorphicOrderAt (frobeniusStickelbergerDetMulSigmaCube L w) 0 := by
  obtain ⟨m, hm, hgm⟩ := exists_twistedGamma_eq_sq_mul_analytic L w he ho hz hs
  have hfun : frobeniusStickelbergerDetMulSigmaCube L w = (fun y : ℂ => y ^ 2) * m := funext fun y => hgm y
  have hmer : MeromorphicAt (fun y : ℂ => y ^ 2) 0 := (analyticAt_id.pow 2).meromorphicAt
  have h2 : meromorphicOrderAt (fun y : ℂ => y ^ 2) 0 = ((2 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff hmer).2
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun y => by simp⟩
  rw [hfun, meromorphicOrderAt_mul hmer hm.meromorphicAt, h2]
  have h3 := hm.meromorphicOrderAt_nonneg
  calc (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) + 0 := by norm_cast
    _ ≤ ((2 : ℤ) : WithTop ℤ) + meromorphicOrderAt m 0 := add_le_add le_rfl h3
end Formalism.L2.Th1.F.SigmaAdditionFormula
