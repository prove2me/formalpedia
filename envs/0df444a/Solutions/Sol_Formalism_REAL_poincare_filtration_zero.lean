-- Prove2me | solution 1 for Formalism.REAL.poincare_filtration_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:12.550063+00:00
-- url     : https://prove2.me/submissions/e2e1aa71-e0de-4675-9e56-4a0e289e1f02

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_ew_nil
import Theorems.Thm_Formalism_REAL_word_action_mem_pfil

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution : pfil ε E u 0 = kSpan ε E u := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨w, hw, hnc, y, hy, rfl⟩
    cases w with
    | nil => rw [SetLike.mem_coe, ew_nil]; exact hy
    | cons p w => simp at hw
  · intro y hy
    have h0 := word_action_mem_pfil ε E u 0 [] (le_refl _) (by intro p hp; cases hp) y hy
    rw [ew_nil] at h0
    exact h0
end Formalism.REAL
