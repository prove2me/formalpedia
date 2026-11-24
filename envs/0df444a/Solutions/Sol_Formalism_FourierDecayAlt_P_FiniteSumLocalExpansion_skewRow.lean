-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.skewRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:53:52.446676+00:00
-- url     : https://prove2.me/submissions/75d9a927-8524-449a-af81-9d5c05ea0f32

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Grp_val_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_qm_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (τ : Equiv.Perm (Fin t)) :
    qminorOp (Q.EH k r) (a ∘ τ) b u Φ g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • qminorOp (Q.EH k r) a b u Φ g := by
  have hτ : ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  rw [FourTermExpansion.qm_eq, FourTermExpansion.qm_eq, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  show ((Equiv.Perm.sign σ : ℤ) : ℂ) • FourTermExpansion.PP a b u (τ * σ) Φ g = _
  simp only [Equiv.coe_mulLeft, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, hτ,
    one_mul]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
