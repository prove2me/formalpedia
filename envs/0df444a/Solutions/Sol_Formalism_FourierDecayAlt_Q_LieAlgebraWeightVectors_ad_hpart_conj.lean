-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_hpart_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:05.721802+00:00
-- url     : https://prove2.me/submissions/319614a8-239c-410c-80d6-08222a94cbfa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_h
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {g : Mx k r} (hg : gᴴ * Hpk k r * g = Hpk k r) (hgi : g * g⁻¹ = 1) (Z : Mx k r) :
    hpart1 (Hpk k r) (g * Z * g⁻¹) = g * hpart1 (Hpk k r) Z * g⁻¹ ∧
      hpart2 (Hpk k r) (g * Z * g⁻¹) = g * hpart2 (Hpk k r) Z * g⁻¹ := by
  have hH : Hpk k r * Hpk k r = 1 := hpk_sq'
  have e1 : gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
    calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hgi, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  have e2 : Hpk k r * (g⁻¹)ᴴ = g * Hpk k r := by
    have h := congrArg Matrix.conjTranspose e1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_h] at h

    calc Hpk k r * (g⁻¹)ᴴ = Hpk k r * ((g⁻¹)ᴴ * Hpk k r) * Hpk k r := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = Hpk k r * (Hpk k r * g) * Hpk k r := by rw [h]
      _ = _ := by rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
  have key : (Hpk k r)⁻¹ * (g * Z * g⁻¹)ᴴ * Hpk k r = g * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * g⁻¹ := by
    rw [hpk_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc Hpk k r * ((g⁻¹)ᴴ * (Zᴴ * gᴴ)) * Hpk k r = (Hpk k r * (g⁻¹)ᴴ) * Zᴴ * (gᴴ * Hpk k r) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, e2]; simp only [Matrix.mul_assoc]
  unfold hpart1 hpart2
  rw [key]
  constructor
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
