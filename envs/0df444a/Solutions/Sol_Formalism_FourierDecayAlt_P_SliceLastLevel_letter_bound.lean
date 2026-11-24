-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.letter_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:46:55.899638+00:00
-- url     : https://prove2.me/submissions/b828da32-e8d4-4445-901d-c4cc8ea87d18

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_norm_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_gN_inv_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_block_embedding_skew_hermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_nset_gv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_levelEmbed_entry_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_gN_le_of_EB


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {n : B.Mat k r} (hn : n ∈ Nset k r) {Y : B.Mat k 0} (hY : B.unitLie k 0 Y) :
    B.inLie k r (n⁻¹ * emb0 k r Y * n) ∧
      ‖n⁻¹ * emb0 k r Y * n‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n ^ 2 := by
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_conj (block_embedding_skew_hermitian hY.1) (nset_gv hn), ?_⟩
  have h1 := norm_le_gN (n⁻¹ * emb0 k r Y * n)
  have h2 := gN_mul_le (n⁻¹ * emb0 k r Y) n
  have h3 := gN_mul_le n⁻¹ (emb0 k r Y)
  have h4 : B.gN (emb0 k r Y) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * 1 :=
    Formalism.FourierDecayAlt.P.Ux5.gN_le_of_EB (emb0 k r Y) (levelEmbed_entry_bound hY) zero_le_one
  rw [gN_inv_GV (nset_gv hn)] at h3
  have hn0 : 0 ≤ B.gN n := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn))
  calc ‖n⁻¹ * emb0 k r Y * n‖ ≤ B.gN (n⁻¹ * emb0 k r Y) * B.gN n := h1.trans h2
    _ ≤ (B.gN n * B.gN (emb0 k r Y)) * B.gN n := by gcongr
    _ ≤ (B.gN n * (((2 * r + k + 1 : ℕ) : ℝ) * 1)) * B.gN n := by gcongr
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n ^ 2 := by ring
end Formalism.FourierDecayAlt.P.SliceLastLevel
