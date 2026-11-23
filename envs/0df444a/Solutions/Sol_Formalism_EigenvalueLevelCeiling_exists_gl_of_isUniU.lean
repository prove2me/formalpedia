-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.exists_gl_of_isUniU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:01.381212+00:00
-- url     : https://prove2.me/submissions/28dd5e1b-4fed-45b1-9cda-4a0c8678a62b

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : IsUniU M) :
    ∃ g : GL (Fin (n + 1)) k, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = M := by
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular (by intro i j hij; exact hM.2 i j hij)]
    simp [hM.1]
  exact ⟨Matrix.nonsingInvUnit M (by rw [hdet]; exact isUnit_one), rfl⟩
end Formalism.EigenvalueLevelCeiling
