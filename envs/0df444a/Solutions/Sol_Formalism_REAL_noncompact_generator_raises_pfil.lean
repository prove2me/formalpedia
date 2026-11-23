-- Prove2me | solution 1 for Formalism.REAL.noncompact_generator_raises_pfil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:11.91111+00:00
-- url     : https://prove2.me/submissions/f9730e23-5318-4d89-88b3-b89f31776e34

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_ew_cons

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
theorem _root_.solution (j : ℕ) (a b : Fin n) (hab : ε a ≠ ε b) :
    ∀ x ∈ pfil ε E u j, E a b x ∈ pfil ε E u (j + 1) := by
  have key : pfil ε E u j ≤ (pfil ε E u (j + 1)).comap (E a b) := by
    unfold pfil
    rw [Submodule.span_le]
    rintro z ⟨w, hw, hnc, y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.subset_span ⟨(a, b) :: w, ?_, ?_, y, hy, ?_⟩
    · simp only [List.length_cons]; omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hab
      · exact hnc p hp
    · exact (ew_cons E (a, b) w y).symm
  intro x hx
  exact key hx
end Formalism.REAL
