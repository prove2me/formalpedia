-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tgood_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:39.341848+00:00
-- url     : https://prove2.me/submissions/f806774c-8fb9-43c5-9d9b-4497121d935a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_CC

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
theorem _root_.solution (w : σ → ℕ) (c : ℕ) : TGood w c 0 (1 : Polynomial (MvPolynomial σ ℂ)) := by
  have := tgood_CC w c 1
  rwa [C_1, Polynomial.C_1] at this
end Formalism.L2.SG.Pf.ColDictValCPf
