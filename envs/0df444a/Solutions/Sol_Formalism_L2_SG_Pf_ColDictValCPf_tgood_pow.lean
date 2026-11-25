-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tgood_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:02.922549+00:00
-- url     : https://prove2.me/submissions/6470e4b6-123d-4820-9af3-9a018d44c523

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_mul
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
variable {σ : Type*}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (w : σ → ℕ) (c : ℕ) {d : ℕ} {F : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d F) (k : ℕ) : TGood w c (k * d) (F ^ k) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact tgood_one w c
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact tgood_mul w c ih hF
end Formalism.L2.SG.Pf.ColDictValCPf
