-- Prove2me | solution 1 for Formalism.GM.TM.yZ_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:34.369478+00:00
-- url     : https://prove2.me/submissions/09e9091e-7193-4819-8348-8de17e3ce6cf

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_polZ_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution {K r : ℕ} [NeZero r] (LL : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (YZ p (r := r) LL J M).FG :=
  Submodule.FG.of_le (polZ_fg LL) inf_le_right
end Formalism.GM.TM
