-- Prove2me | solution 1 for Formalism.REAL.height_word_shift_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:02.516904+00:00
-- url     : https://prove2.me/submissions/30d8eae7-c7f8-4414-9f86-7aa391dd6009

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_height_functional_add
import Theorems.Thm_Formalism_REAL_height_functional_root

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution {m : ℕ} (w : List (Fin m × Fin m)) (hw : ∀ p ∈ w, p.2 < p.1) :
    0 ≤ heightFunctional (wordWeightShift w) ∧ (w ≠ [] → 0 < heightFunctional (wordWeightShift w)) := by
  induction w with
  | nil => simp [wordWeightShift, heightFunctional]
  | cons p w ih =>
    have h1 := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have h2 : ((p.2 : ℕ) : ℝ) < ((p.1 : ℕ) : ℝ) := by
      exact_mod_cast (hw p List.mem_cons_self)
    simp only [wordWeightShift, height_functional_add, height_functional_root]
    constructor
    · linarith [h1.1]
    · intro _; linarith [h1.1]
end Formalism.REAL
