-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tgood_CC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:19.953158+00:00
-- url     : https://prove2.me/submissions/fc98aad6-0907-427a-8cae-2886bc391ba4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
variable {σ : Type*}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (w : σ → ℕ) (c : ℕ) (r : ℂ) : TGood w c 0 (Polynomial.C (C r)) := by
  classical
  intro j m h
  rw [Polynomial.coeff_C] at h
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, coeff_C] at h
    by_cases hm : 0 = m
    · subst hm; simp
    · rw [if_neg hm] at h; exact absurd rfl h
  · rw [if_neg hj, coeff_zero] at h; exact absurd rfl h
end Formalism.L2.SG.Pf.ColDictValCPf
