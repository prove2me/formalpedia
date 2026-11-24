-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.detOp_pow_apply_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:48.818853+00:00
-- url     : https://prove2.me/submissions/52299290-3201-4ef7-8b10-509ec9cedeed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_detOp_apply_eigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution {F : Type*} [AddCommGroup F] [Module R F] {n : ℕ}
    (D : Fin n → Fin n → Module.End R F) (a : Matrix (Fin n) (Fin n) R) (g : F)
    (hD : ∀ ρ c, D ρ c g = a ρ c • g) (y : ℕ) : ((detOp D) ^ y) g = a.det ^ y • g := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [pow_succ, Module.End.mul_apply, detOp_apply_eigen D a g hD, map_smul, ih, smul_smul, pow_succ]
    congr 1
    ring
end Formalism.L2.FormalSeriesBounds.S4
