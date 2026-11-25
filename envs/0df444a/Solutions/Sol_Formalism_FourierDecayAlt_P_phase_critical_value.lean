-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_critical_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:27.238108+00:00
-- url     : https://prove2.me/submissions/c94fd205-9280-4fdd-a48a-2f3cd0fc4b3f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.CritValue := by
  intro K _ m z
  unfold g0
  simp only [Finset.sum_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : Ring.inverse ((z : K) ^ m) = ((z⁻¹ : Kˣ) : K) ^ m := by
    rw [← Units.val_pow_eq_pow_val, Ring.inverse_unit, ← Units.val_pow_eq_pow_val, inv_pow]
  rw [this, pow_succ, mul_assoc, mul_comm (z : K), ← mul_assoc, ← mul_pow]
  simp [add_mul]
end Formalism.FourierDecayAlt.P
