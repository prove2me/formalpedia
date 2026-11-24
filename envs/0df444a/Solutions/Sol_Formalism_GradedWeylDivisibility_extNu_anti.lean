-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.extNu_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:54.297943+00:00
-- url     : https://prove2.me/submissions/5d3e5ab3-4787-48ee-8728-5c2d1fd35c52

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRowWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {n : ℕ} {ν : Fin n → ℕ} (hν : Antitone ν) {i j : ℕ} (hij : i ≤ j) :
    hwrowExtNu ν j ≤ hwrowExtNu ν i := by
  unfold hwrowExtNu
  by_cases hj : j < n
  · have hi : i < n := lt_of_le_of_lt hij hj
    rw [dif_pos hj, dif_pos hi]
    first
    | exact hν (Fin.mk_le_mk.2 hij)
    | exact hν (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  · rw [dif_neg hj]
    exact Nat.zero_le _
end Formalism.GradedWeylDivisibility
