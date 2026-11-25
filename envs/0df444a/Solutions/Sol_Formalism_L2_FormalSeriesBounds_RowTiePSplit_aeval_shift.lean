-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.aeval_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:19.559638+00:00
-- url     : https://prove2.me/submissions/4eac88ce-e6c2-42ba-a205-918d54de0069

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_alg_mulVec
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_pow_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (f : K[X]) :
    aeval (N + B) f *ᵥ w = aeval (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) f *ᵥ w := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mulVec, Matrix.add_mulVec, hp, hq]
  | monomial k a _ =>
    rw [map_mul, map_mul, aeval_C, aeval_C, map_pow, map_pow, aeval_X, aeval_X, alg_mulVec, alg_mulVec,
      pow_shift N B hNB lam w hw (k + 1)]
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
