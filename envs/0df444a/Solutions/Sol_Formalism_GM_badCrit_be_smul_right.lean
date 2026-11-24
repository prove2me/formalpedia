-- Prove2me | solution 1 for Formalism.GM.badCrit_be_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:10.96081+00:00
-- url     : https://prove2.me/submissions/9dba2ca3-b030-4bcd-ae9a-334bac4574cb

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
theorem _root_.solution (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (c : ℤ_[p]) (x y : Vs) :
    be x (c • y) = (c : ℚ_[p]) * be x y := by
  rw [badCrit_smul_eq, map_smul, smul_eq_mul]
end Formalism.GM
