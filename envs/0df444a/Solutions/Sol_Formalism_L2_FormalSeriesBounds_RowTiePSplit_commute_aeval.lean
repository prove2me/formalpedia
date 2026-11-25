-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.commute_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:28.835068+00:00
-- url     : https://prove2.me/submissions/fc998ec2-d16e-482a-826b-5b5be62f8e50

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA

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
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) K} (h : Commute A B) (f : K[X]) : Commute A (aeval B f) := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (Algebra.commutes a A).symm
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact ih.mul_right h
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
