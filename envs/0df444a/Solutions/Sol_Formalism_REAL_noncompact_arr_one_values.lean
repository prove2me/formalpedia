-- Prove2me | solution 1 for Formalism.REAL.noncompact_arr_one_values
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:58.13479+00:00
-- url     : https://prove2.me/submissions/fafb98e0-d7ba-46a9-ae1a-1ab0dc9582f0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_mem_noncompact_arr_iff_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n 1}
    (hF : F ∈ arrV0 ε E u 1) (a b : Fin n) :
    (ε a ≠ ε b → F (fun _ => (a, b)) ∈ kSpan ε E u) ∧ (ε a = ε b → F (fun _ => (a, b)) = 0) := by
  have h := (mem_noncompact_arr_iff_general F).mp hF (fun _ => (a, b))
  constructor
  · intro hne
    rwa [if_pos (fun _ => hne)] at h
  · intro he
    rw [if_neg (fun h' => h' 0 he), Submodule.mem_bot] at h
    exact h
end Formalism.REAL
