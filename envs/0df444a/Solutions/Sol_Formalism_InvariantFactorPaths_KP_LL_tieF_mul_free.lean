-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.tieF_mul_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:55.338213+00:00
-- url     : https://prove2.me/submissions/1448ce2f-396e-4b29-b4eb-2c8967ac0596

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
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
private lemma pderiv_mul_of_pderiv_eq_zero (i : σ) (q f : MvPolynomial σ k) (h : pderiv i q = 0) :
    pderiv i (q * f) = q * pderiv i f := by
  rw [Derivation.leibniz, h, smul_zero, add_zero, smul_eq_mul]
end
end Formalism.InvariantFactorPaths.KP.LL
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0) (he : ∀ c, pderiv (e c) q = 0) :
    tieF w e (q * f) = q * tieF w e f := by
  have key : ∀ g : MvPolynomial σ k, tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by
    intro g
    simp [tieF]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pderiv_mul_of_pderiv_eq_zero _ _ _ (he c), pderiv_mul_of_pderiv_eq_zero _ _ _ (hw c)]
end Formalism.InvariantFactorPaths.KP.LL
