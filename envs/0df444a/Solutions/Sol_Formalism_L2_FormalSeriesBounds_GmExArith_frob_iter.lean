-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.frob_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:07:48.884809+00:00
-- url     : https://prove2.me/submissions/042185bc-4a1b-4261-b6bb-89c636c706fe

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_pow_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (ψ : ZMod d → R →+* C) (hint : ∀ a x, V.Ge 0 (ψ a x))
    (frob : ∀ a x, V.MM (ψ (a + 1) x - ψ a x ^ V.l)) (x : R) (j : ℕ) :
    V.MM (ψ (j : ZMod d) x - ψ 0 x ^ (V.l ^ j)) := by
  induction j with
  | zero => rw [Nat.cast_zero, pow_zero, pow_one, sub_self]; exact mm_zero
  | succ j ih =>
    have e : ψ ((j + 1 : ℕ) : ZMod d) x - ψ 0 x ^ (V.l ^ (j + 1)) =
        (ψ ((j : ZMod d) + 1) x - ψ (j : ZMod d) x ^ V.l) +
          (ψ (j : ZMod d) x ^ V.l - (ψ 0 x ^ (V.l ^ j)) ^ V.l) := by
      rw [Nat.cast_succ, ← pow_mul, ← pow_succ]; ring
    rw [e]
    exact mm_add (frob _ x) (mm_pow_sub (hint _ x) ((hint 0 x).pow _) ih V.l)
end Formalism.L2.FormalSeriesBounds.GmExArith
