-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lower_parabolic_entry_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:41:04.897477+00:00
-- url     : https://prove2.me/submissions/3e0746a8-0a7e-4eda-9013-fa677fa2f62c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetSubmatrixUnitriangularEqOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_monomialMatrix_conj_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 CardInsertEmbedding DeterminantReindex
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LPg (C2.monoP w d)) (x y : Fin m) (hxy : x < y) :
    l (w x) (w y) = 0 := by
  have := hl.2.1 x y hxy
  rw [monomialMatrix_conj_apply w d hd] at this
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (inv_ne_zero (hd x))
    · exact h'
  · exact absurd h (hd y)
end Formalism.FourierDecayAlt.P
