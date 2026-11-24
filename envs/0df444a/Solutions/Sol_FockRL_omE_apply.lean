-- Prove2me | solution 1 for FockRL.omE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:40.469834+00:00
-- url     : https://prove2.me/submissions/b2d049bd-43c2-4928-a95e-0cebd68057a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open FockRL
variable {p q r s : ℕ}
namespace FockRL
theorem _root_.solution (l l' : FockH1Action.Ln p q r s) (P : FockH1Action.Pol p q r s) :
    FockH1Action.omE l l' P = FockH1Action.raiB l (FockH1Action.lowB l' P) + if l = l' then (1 / 2 : ℂ) • P else 0 := by
  simp only [FockH1Action.omE]
  split_ifs <;> rfl
end FockRL
