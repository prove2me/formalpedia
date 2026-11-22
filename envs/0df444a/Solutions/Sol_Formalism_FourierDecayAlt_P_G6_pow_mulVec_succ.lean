-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G6.pow_mulVec_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:06.140363+00:00
-- url     : https://prove2.me/submissions/ee922ab3-eec2-433a-94e5-b6ffe307edcd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G6
theorem _root_.solution {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) (k : Fin m) : (X ^ m *ᵥ B) k.succ = 0 := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [pow_apply_eq_zero hX m k.succ l (by have := l.2; simp only [Fin.val_succ]; omega), zero_mul]
end Formalism.FourierDecayAlt.P.G6
