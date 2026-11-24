-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.symplectic_transpose_entry_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:09.854389+00:00
-- url     : https://prove2.me/submissions/21de3a77-e0a7-4aba-8423-3bf45745eb8f

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SymplecticTransposeEntryZeroOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.Y
section Helpers
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
private theorem mul_J_mul_transpose_apply_fin_two (b a : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (b * Formalism.YangianSpanCharacter.T.J A * aᵀ) i j = b i 0 * a j 1 - b i 1 * a j 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J]
  noncomm_ring
end Helpers
end Formalism.YangianSpanCharacter.P
end

set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution {t : 𝕜 → Matrix (Fin 2) (Fin 2) A} {q : 𝕜 → 𝕜}
    (h : ∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) (Y : 𝕜) :
    t Y 1 1 * t (Y + 1) 1 0 = t Y 1 0 * t (Y + 1) 1 1 := by
  have h1 : t Y 1 0 * t (Y + 1) 1 1 - t Y 1 1 * t (Y + 1) 1 0 = 0 := by
    have e := congrFun (congrFun (h Y) 1) 1
    rw [mul_J_mul_transpose_apply_fin_two] at e
    rw [e]
    simp [Formalism.YangianSpanCharacter.T.J]
  exact (sub_eq_zero.mp h1).symm
end Formalism.YangianSpanCharacter.P
