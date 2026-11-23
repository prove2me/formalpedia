-- Prove2me | solution 1 for DiscrNeWork.zeta6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:14.647777+00:00
-- url     : https://prove2.me/submissions/864afb5f-7ec2-4f6f-afb5-15404938dad0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
import Theorems.Thm_DiscrNeWork_bern6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork
namespace DiscrNeWork
theorem _root_.solution : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (show (3 : ℕ) ≠ 0 by norm_num)
  rw [show (6 : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h, bern6]
  norm_num [Nat.factorial]
  ring
end DiscrNeWork
