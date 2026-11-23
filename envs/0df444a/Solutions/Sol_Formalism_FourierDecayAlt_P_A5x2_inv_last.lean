-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.inv_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:11.187551+00:00
-- url     : https://prove2.me/submissions/8c472dba-292c-4cde-aa27-511e947aac06

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_low_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_mono
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_mul_ptI
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution {K : Type} [CommRing K] (S : List ℕ) (T : ℕ → Kˣ)
    (x y : Matrix (Fin S.sum) (Fin S.sum) K) (hx : IsLowUni x) (hy : IsUpUni y)
    (a b c : Fin S.sum) (hb : b.val + 1 = S.sum) (hc : revF S c = b) :
    (x * pt S T * y)⁻¹ a b = (((T (blk S c))⁻¹ : Kˣ) : K) * y⁻¹ a c := by
  have hinv : (x * pt S T * y)⁻¹ = y⁻¹ * ptI S T * x⁻¹ := by
    apply Matrix.inv_eq_right_inv
    calc x * pt S T * y * (y⁻¹ * ptI S T * x⁻¹)
        = x * (pt S T * ((y * y⁻¹) * ptI S T)) * x⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [mul_inv_one_up hy, Matrix.one_mul, pt_mul_ptI, Matrix.mul_one, mul_inv_one_low hx]
  have hxi := isLowUni_inv K hx
  have hbc : revF S b = c := by rw [← hc, revF_revF]
  rw [hinv, Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [hxi.2 b, mul_one, ptI, mul_mono, hbc, mul_comm]
  · intro k _ hk
    have : k < b := by
      rw [Fin.lt_def]
      have h1 := k.2
      have h2 : k.val ≠ b.val := fun h => hk (Fin.ext h)
      omega
    rw [low_zero hxi this, mul_zero]
  · simp
end Formalism.FourierDecayAlt.P.A5x2
