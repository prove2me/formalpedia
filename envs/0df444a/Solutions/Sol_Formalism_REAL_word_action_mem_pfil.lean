-- Prove2me | solution 1 for Formalism.REAL.word_action_mem_pfil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:12.681573+00:00
-- url     : https://prove2.me/submissions/1f610911-0a2f-4236-b6ea-d74bc50a2a98

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

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
theorem _root_.solution (j : ℕ) (w : List (Fin n × Fin n)) (hw : w.length ≤ j)
    (hnc : ∀ p ∈ w, ε p.1 ≠ ε p.2) (y : V) (hy : y ∈ kSpan ε E u) : ew E w y ∈ pfil ε E u j := by
  unfold pfil
  exact Submodule.subset_span ⟨w, hw, hnc, y, hy, rfl⟩
end Formalism.REAL
