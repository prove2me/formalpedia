-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.diagonal_entry_eq_of_modular_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:09.473868+00:00
-- url     : https://prove2.me/submissions/409cc7d6-c603-4a18-af36-ee1cc0eb890e

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_qdet_mod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution (H : ModHyp t τinv q S) {u : 𝕜} (hu : u ∈ S) (hu1 : u + 1 ∈ S) :
    t u 0 0 = t u 1 1 * (mf t τinv u * lf t τinv u + hf τinv q u) := by
  have hq := qdet_mod H hu hu1
  have hinv := (H.2.2.2.1 u hu).1
  have hx : t u 1 1 * (τinv u * t u 0 1 * (τinv u * t u 1 0)) = t u 0 1 * τinv u * t u 1 0 := by
    calc t u 1 1 * (τinv u * t u 0 1 * (τinv u * t u 1 0))
        = t u 1 1 * τinv u * t u 0 1 * (τinv u * t u 1 0) := by simp only [mul_assoc]
      _ = t u 0 1 * τinv u * t u 1 0 := by rw [hinv, one_mul, mul_assoc]
  simp only [mf, lf, hf]
  rw [mul_add, mul_smul_comm, ← mul_assoc (t u 1 1) (τinv u) (τinv (u + 1)), hinv, one_mul, hx,
    ← hq]
  abel
end Formalism.YangianSpanCharacter.P
