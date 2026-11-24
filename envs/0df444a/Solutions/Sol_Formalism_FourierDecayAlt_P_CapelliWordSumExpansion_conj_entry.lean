-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:56.307271+00:00
-- url     : https://prove2.me/submissions/338b9747-1d8f-4fe9-a7b8-a10a17e55498

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_hpk_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution (a b i j : Fin (2 * r + k + 1)) :
    ‖((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j‖ ≤ 1 := by
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, Matrix.conjTranspose_single, star_one]
  have e : (Hpk k r * Matrix.single b a (1 : ℂ) * Hpk k r) i j = Hpk k r i b * Hpk k r a j := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, Finset.sum_ite_eq]
  rw [e, norm_mul]
  exact mul_le_one₀ (hpk_entry i b) (norm_nonneg _) (hpk_entry a j)
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
