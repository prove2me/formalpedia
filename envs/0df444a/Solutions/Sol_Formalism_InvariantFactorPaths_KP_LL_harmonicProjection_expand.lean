-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.harmonicProjection_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:39.739034+00:00
-- url     : https://prove2.me/submissions/9560bb78-288e-4bdf-b36c-4b6a8008d6a7

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_mulLeft_pow_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieF_pow_mul_free
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
private lemma pderiv_X_pow_of_ne' (i j : σ) (h : i ≠ j) (n : ℕ) : pderiv i (X j ^ n : MvPolynomial σ k) = 0 := by
  classical
  rw [Derivation.leibniz_pow]
  simp [pderiv_X, Pi.single_apply, Ne.symm h]
end
end Formalism.InvariantFactorPaths.KP.LL
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k) :
    M.tieP w e zv sv o n z x = ∑ m ∈ range (o + 1),
      (((-1 : k) ^ m) / (((m.factorial : k) ^ 2) * ((o + n + r + z - 1).choose m : k))) •
        (ehP w e zv sv ^ m * (X zv ^ z * (tieF w e ^ m) x)) := by
  have hE : ∀ (m : ℕ) (y : MvPolynomial σ k),
      (M.tieEh w e zv sv ^ m) y = ehP w e zv sv ^ m * y := by
    intro m y
    unfold M.tieEh
    exact mulLeft_pow_apply _ _ m
  unfold M.tieP
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [tieF_pow_mul_free w e _ x (fun c => pderiv_X_pow_of_ne' _ _ (hz c).1 z)
    (fun c => pderiv_X_pow_of_ne' _ _ (hz c).2 z) m, hE]
end Formalism.InvariantFactorPaths.KP.LL
