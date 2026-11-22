-- Prove2me | solution 1 for Formalism.REAL.f1alg_inG_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:54:47.252816+00:00
-- url     : https://prove2.me/submissions/b7d43b6f-e6fd-4832-87b3-2aa995f39d40

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ Xᴴ = -(Jm ε * X * Jm ε) := by
  unfold inG
  constructor
  · intro h
    have h' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h', Matrix.neg_mul]
  · intro h
    rw [h, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one, neg_add_cancel]
end Formalism.REAL
