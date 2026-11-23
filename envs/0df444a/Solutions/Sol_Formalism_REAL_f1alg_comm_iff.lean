-- Prove2me | solution 1 for Formalism.REAL.f1alg_comm_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:40.480287+00:00
-- url     : https://prove2.me/submissions/7bb7f5dd-fd01-4877-9563-55528d205d24

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_JJ_left
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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = Jm ε * A ↔ Jm ε * A * Jm ε = A := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, f1alg_JJ_left]
  · intro h
    calc A * Jm ε = (Jm ε * A * Jm ε) * Jm ε := by rw [h]
      _ = Jm ε * A := by rw [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]
end Formalism.REAL
