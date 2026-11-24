-- Prove2me | solution 1 for Formalism.GM.badCrit_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:35.730085+00:00
-- url     : https://prove2.me/submissions/42a3112c-b85e-4c0e-ba9c-d54a600230b2

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
import Theorems.Thm_Formalism_GM_badCrit_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
namespace Formalism.GM
theorem _root_.solution : Module.IsTorsionFree ℤ_[p] Vs :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
    rw [badCrit_smul_eq, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (PadicInt.ext (h.trans PadicInt.coe_zero.symm))
    · exact Or.inr h
end Formalism.GM
