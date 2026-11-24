-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_from_blocks_single_regular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:33.693369+00:00
-- url     : https://prove2.me/submissions/2f108000-618d-43c7-8a68-3a780ef973c7

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_add_smul_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Matrix Polynomial
variable {R : Type} [CommRing R]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (r : ℕ) (W Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (l : Fin (r + 1))
    (t t' : R) (hreg : IsRegular W.det) :
    (fromBlocks W ((-t) • Matrix.single l l (1 : R)) ((-t') • Matrix.single l l (1 : R)) Z).det =
      W.det * Z.det - t * t' * W.adjugate l l * Z.adjugate l l := by
  set A := (-t) • Matrix.single l l (1 : R) with hA
  set D := (-t') • Matrix.single l l (1 : R) with hD
  set δ := W.det with hδ
  have h : fromBlocks W A D Z * fromBlocks W.adjugate (-(W.adjugate * A)) 0 (δ • 1) =
      fromBlocks (δ • 1) 0 (D * W.adjugate) (δ • Z - D * W.adjugate * A) := by
    rw [fromBlocks_multiply]
    congr 1
    · simp [mul_adjugate, hδ]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, mul_adjugate]; simp [hδ]
    · simp
    · simp [Matrix.mul_assoc]; abel
  have hDA : D * W.adjugate * A = (t * t' * W.adjugate l l) • Matrix.single l l (1 : R) := by
    rw [hA, hD]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.single_mul_mul_single, smul_smul]
    ext a b
    simp [Matrix.single_apply]
  have h2 := congrArg det h
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, hDA, sub_eq_add_neg, ← neg_smul,
    det_add_smul_single, det_adjugate, det_smul, det_smul, adjugate_smul] at h2
  simp only [Fintype.card_fin, add_tsub_cancel_right, det_one, mul_one, Matrix.smul_apply,
    smul_eq_mul] at h2
  apply (hreg.pow (2 * r + 1)).left
  simp only
  linear_combination h2
end Formalism.HermitianLatticeCounting.P
