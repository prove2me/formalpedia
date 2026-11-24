-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.cW_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:35:12.566705+00:00
-- url     : https://prove2.me/submissions/6fadaff4-265b-4279-9ba4-8f69ee8de032

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_cW_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Scale
open PowerSeries
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution {K : Type} [Field K] (g2 g3 lam : K) (k : ℕ) :
    cW (lam ^ 4 * g2) (lam ^ 6 * g3) k = lam ^ (2 * k) * cW g2 g3 k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_eq, cW_eq g2 g3 k]
    split_ifs with h2 h3 h4
    · subst h2; ring
    · subst h3; ring
    · rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.isLt
      rw [ih (m.val + 2) (by omega), ih (k - (m.val + 2)) (by omega)]
      have e : lam ^ (2 * k) = lam ^ (2 * (m.val + 2)) * lam ^ (2 * (k - (m.val + 2))) := by
        rw [← pow_add]; congr 1; omega
      rw [e]; ring
    · rw [mul_zero]
end Formalism.L2.Th1.F.Scale
