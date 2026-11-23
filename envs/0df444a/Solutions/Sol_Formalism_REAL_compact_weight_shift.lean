-- Prove2me | solution 1 for Formalism.REAL.compact_weight_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:41.167026+00:00
-- url     : https://prove2.me/submissions/c325d5ff-1694-4452-8577-dcaf3e7462cd

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_lie_commutator

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
theorem _root_.solution (h : KRel ε F) {ν : Fin n → ℝ} {y : V} (hy : IsWeight F ν y) {c d : Fin n}
    (hcd : ε c = ε d) : IsWeight F (ν + Pi.single c 1 - Pi.single d 1) (F c d y) := by
  intro a
  have := compact_lie_commutator h (a := a) (b := a) rfl hcd y
  rw [hy a, map_smul, sub_eq_iff_eq_add] at this
  rw [this]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  rcases eq_or_ne a c with h1 | h1 <;> rcases eq_or_ne d a with h2 | h2
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2, add_smul]; abel
  · subst h2; simp [h1, sub_smul]; abel
  · simp [h1, h2, Ne.symm h2]
end Formalism.REAL
