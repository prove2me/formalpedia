-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.EHc_eq_LT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:19.774328+00:00
-- url     : https://prove2.me/submissions/beb5a26b-3bee-491b-9276-df100216b3ec

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hinv
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    (Hpk k r)⁻¹ * (y⁻¹ * Z * y)ᴴ * Hpk k r = y⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * y := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hinvH : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hHH
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  rw [hinvH, hinv]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
    hHH, mul_one, hHH']
private theorem hermitian_half_one_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    hpart1 (Hpk k r) (y⁻¹ * Z * y) = y⁻¹ * hpart1 (Hpk k r) Z * y := by
  unfold hpart1
  rw [Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]
private theorem hermitian_half_two_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    hpart2 (Hpk k r) (y⁻¹ * Z * y) = y⁻¹ * hpart2 (Hpk k r) Z * y := by
  unfold hpart2
  rw [Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution (y : Mat k r) (hy : y ∈ GV k r) :
    Formalism.FourierDecayAlt.P.JFxB.EHc (E := E) k r y = FourTermExpansion.LT (Mc y) := by
  funext c d f g
  show RdV (y⁻¹ * hpart1 (Hpk k r) (Matrix.single c d 1) * y) f g +
      Complex.I • RdV (y⁻¹ * hpart2 (Hpk k r) (Matrix.single c d 1) * y) f g =
    RdV (hpart1 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g +
      Complex.I • RdV (hpart2 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g
  rw [hermitian_half_one_conj_of_mem_GV hy, hermitian_half_two_conj_of_mem_GV hy]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
