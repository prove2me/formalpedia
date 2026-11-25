-- Prove2me | solution 1 for Formalism.REAL.f1alg_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:37.319086+00:00
-- url     : https://prove2.me/submissions/173a3c7b-1e61-46c6-b9b2-6ea5649d1999

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace Formalism.REAL
private lemma Jm_mul_self_eq_oneRealPlaceTaylor {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : A * Jm ε = B * Jm ε) : A = B := by
  have h2 := congrArg (· * Jm ε) h
  simpa [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor] using h2
end Formalism.REAL
