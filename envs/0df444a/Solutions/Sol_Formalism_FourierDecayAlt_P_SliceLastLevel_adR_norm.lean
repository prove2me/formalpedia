-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.adR_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:47:03.8968+00:00
-- url     : https://prove2.me/submissions/41e54396-5bbc-4e97-9e5b-904fdb40ae11

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Lt_unit
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
open scoped ContDiff
set_option linter.style.haveILetI false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {n' : B.Mat k r} (hn' : n' ∈ B.GV k r) (i : Formalism.FourierDecayAlt.P.Ux10.J k r) :
    ‖adR n' i‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n' ^ 2 := by
  have hEB : Formalism.FourierDecayAlt.P.Ux5.EB (Formalism.FourierDecayAlt.P.Ux10.Lt i) 1 := fun a b => (Formalism.FourierDecayAlt.P.Ux10.Lt_unit i).2 a b
  have h1 := norm_le_gN (adR n' i)
  have h2 := gN_mul_le (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i) n'
  have h3 := gN_mul_le n'⁻¹ (Formalism.FourierDecayAlt.P.Ux10.Lt i)
  have h4 : B.gN (Formalism.FourierDecayAlt.P.Ux10.Lt i) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * 1 :=
    Formalism.FourierDecayAlt.P.Ux5.gN_le_of_EB _ hEB zero_le_one
  rw [gN_inv_GV hn'] at h3
  have hn0 : 0 ≤ B.gN n' := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hn')
  calc ‖adR n' i‖ ≤ B.gN (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i) * B.gN n' := h1.trans h2
    _ ≤ (B.gN n' * B.gN (Formalism.FourierDecayAlt.P.Ux10.Lt i)) * B.gN n' := by gcongr
    _ ≤ (B.gN n' * (((2 * r + k + 1 : ℕ) : ℝ) * 1)) * B.gN n' := by gcongr
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n' ^ 2 := by ring
end Formalism.FourierDecayAlt.P.SliceLastLevel
