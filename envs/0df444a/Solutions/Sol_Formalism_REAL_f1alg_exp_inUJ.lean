-- Prove2me | solution 1 for Formalism.REAL.f1alg_exp_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:00.174977+00:00
-- url     : https://prove2.me/submissions/2ce5e4ac-f1c7-4269-91a7-0b262ca4ef35

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_JJ_left
import Theorems.Thm_Formalism_REAL_f1alg_inG_iff
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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  unfold inUJ
  have hY' : Yᴴ = Jm ε * (-Y) * Jm ε := by
    rw [(f1alg_inG_iff ε Y).mp hY, Matrix.mul_neg, Matrix.neg_mul]
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, Jm_mul_self_eq_oneRealPlaceTaylor ε, Jm_mul_self_eq_oneRealPlaceTaylor ε⟩
  have hconj : NormedSpace.exp (Jm ε * (-Y) * Jm ε) = Jm ε * NormedSpace.exp (-Y) * Jm ε :=
    Matrix.exp_units_conj U (-Y)
  have hinv : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hY', hconj]
  simp only [Matrix.mul_assoc]
  rw [f1alg_JJ_left, hinv, Matrix.mul_one]
end Formalism.REAL
