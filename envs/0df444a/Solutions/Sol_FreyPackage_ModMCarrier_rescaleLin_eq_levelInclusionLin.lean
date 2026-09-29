-- Prove2me | solution 1 for FreyPackage.ModMCarrier.rescaleLin_eq_levelInclusionLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/00c3bdcc-2900-56b8-975f-7f9ff99efa6f

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin

set_option autoImplicit false

open CongruenceSubgroup
open ModularForm

theorem solution {R M : ℕ} [NeZero M]
    (h : 1 * R ∣ M) (hRM : R ∣ M) (k : ℤ) (f : CuspForm (Gamma0 R) k) :
    FreyPackage.ModMCarrier.rescaleLin h k f = FreyPackage.ModMCarrier.levelInclusionLin hRM k f := by
  have h1 : heckeDiagMatrix 1 = 1 := by
    apply Units.ext
    rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine DFunLike.coe_injective ?_
  change ⇑(FreyPackage.ModMCarrier.rescaleLin h k f) = ⇑(FreyPackage.ModMCarrier.levelInclusionLin hRM k f)
  rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, FreyPackage.ModMCarrier.coe_levelInclusionLin, h1,
    SlashAction.slash_one]

end S_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin
end P2MW
export P2MW.S_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin (solution)
