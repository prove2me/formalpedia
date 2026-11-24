-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.wt_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:46.799802+00:00
-- url     : https://prove2.me/submissions/b0c342a8-913b-4c6f-8bf7-4bc1b6296d37

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hF : F ∈ YCond p LL j M) (m : Fin N × Fin r →₀ ℕ) (hm : m ∈ F.support) :
    ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M := by
  have h := ycond_le p LL j M hF
  rw [mem_restrictSupport_iff] at h
  exact h (Finset.mem_coe.2 hm)
end Formalism.GM.FrozenVariableComponents
