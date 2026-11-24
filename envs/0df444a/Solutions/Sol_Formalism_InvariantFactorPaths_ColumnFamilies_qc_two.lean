-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:51.561798+00:00
-- url     : https://prove2.me/submissions/2491fa69-2d3a-4da3-8673-a7ef81a83ce9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_TMat_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hβ : IsSMu M mu β) (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I)
    {R : Type} [CommRing R] (x g : GL (Fin n) R) (I : TIdx mu) :
    ∑ j, evGL g ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) * evGL x (β j) =
      ∑ j, evGL g ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I) * evGL x (β j) := by
  have e1 : evGL (x * g) (brk mu I) = ∑ j, evGL g ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) * evGL x (β j) := by
    rw [← hph I]
    simp only [map_sum, map_zsmul, hβ.2.2, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul, eq_intCast,
      map_intCast, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : evGL (x * g) (brk mu I) = ∑ j, evGL g ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I) * evGL x (β j) := by
    rw [brk, qc_TMat_mul]
    have : ∀ K, evGL x (TMat mu (canT mu) K) = ∑ j, (ph j K : R) * evGL x (β j) := by
      intro K
      show evGL x (brk mu K) = _
      rw [← hph K]
      simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast]
    simp only [this, map_sum, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul, eq_intCast,
      map_intCast]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [← e1, e2]
end Formalism.InvariantFactorPaths.ColumnFamilies
