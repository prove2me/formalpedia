-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.upJ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:59.403835+00:00
-- url     : https://prove2.me/submissions/6ce4fd1c-8f67-475b-9fef-b9b9d9f526ea

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_upJ_m
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (u b : upUniG K h.1.sum × upUniG K g.1.sum)
    (η ρ : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    upJ hN u η * upJ hN b ρ = (upJ hN (u * b) (ρ + (sec_m b.1)⁻¹ * η * sec_m b.2) :
      upUniG K w.1.sum) := by
  apply sec_m_ext
  have hm : ∀ {n : ℕ} {H : Subgroup (GL (Fin n) K)} (x y : H), sec_m (x * y) = sec_m x * sec_m y :=
    fun _ _ => rfl
  have hi : ∀ M : Matrix (Fin h.1.sum) (Fin g.1.sum) K, sec_m b.1 * ((sec_m b.1)⁻¹ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.coe_units_inv, Units.mul_inv, Matrix.one_mul]
  rw [hm, upJ_m, upJ_m, upJ_m, blkM_mul, Prod.fst_mul, Prod.snd_mul, hm, hm]
  congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hi]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
