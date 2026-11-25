-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU.norm_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:33.416256+00:00
-- url     : https://prove2.me/submissions/395b80ff-9e7e-460f-ab4e-fa2726c11acd

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_LU_norm_adj_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ)
    (hA : ∀ i j, ‖A i j‖ ≤ B) (hdet : δ ≤ ‖A.det‖) (i j : Fin n) :
    ‖A⁻¹ i j‖ ≤ (n.factorial : ℝ) * B ^ n / δ := by
  have hd : A.det ≠ 0 := fun h => by rw [h, norm_zero] at hdet; linarith
  have h1 := norm_adj_le A B hB hA i j
  have h2 := inv_anti₀ hδ hdet
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, norm_mul, norm_inv, div_eq_mul_inv]
  calc ‖A.det‖⁻¹ * ‖A.adjugate i j‖ = ‖A.adjugate i j‖ * ‖A.det‖⁻¹ := mul_comm _ _
    _ ≤ ((n.factorial : ℝ) * B ^ n) * δ⁻¹ := mul_le_mul h1 h2 (by positivity) (by positivity)
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
