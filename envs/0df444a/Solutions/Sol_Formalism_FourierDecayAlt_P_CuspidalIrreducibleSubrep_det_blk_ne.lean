-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_blk_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:02.487358+00:00
-- url     : https://prove2.me/submissions/e9a52575-5c53-4f00-98cb-cb080b8ddc89

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_geom
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_det_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
theorem _root_.solution {n : ℕ} (t : ℂ) (ht : t ≠ 0) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have hdet : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := det_shift X hX t
  have ht' : t ^ n ≠ 0 := pow_ne_zero n ht
  have hinv : IsUnit (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det := by rw [hdet]; exact ht'.isUnit
  letI := (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).invertibleOfIsUnitDet hinv
  have hA : ⅟(t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) = (t ^ n)⁻¹ • geoS X t := by
    apply invOf_eq_right_inv
    rw [Matrix.mul_smul, geom X hX t, smul_smul, inv_mul_cancel₀ ht', one_smul]
  rw [Matrix.det_fromBlocks₁₁, hdet, hA, Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  rw [mul_sub]
  congr 1
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  field_simp
  try ring
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
