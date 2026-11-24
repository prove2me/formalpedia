-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.ad_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:42:29.796962+00:00
-- url     : https://prove2.me/submissions/870bdfe8-80ad-43dd-8dc1-ee590dd1f690

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_sup_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_gN_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


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
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.WeakDominationMajorants
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
theorem _root_.solution {s X : Mat k r} (hs : s ∈ GV k r) (hX : unitLie k r X) :
    ‖s⁻¹ * X * s‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * gN s ^ 2 := by
  refine (sup_le_gN _).trans ?_
  have h1 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (s⁻¹ * X) s
  have h2 := Formalism.FourierDecayAlt.P.B6.gN_mul_le s⁻¹ X
  rw [Orb.gN_inv hs] at h2
  have h3 := gN_unit hX
  have hs0 := Orb.gN_nonneg s
  calc gN (s⁻¹ * X * s) ≤ gN (s⁻¹ * X) * gN s := h1
    _ ≤ (gN s * gN X) * gN s := mul_le_mul_of_nonneg_right h2 hs0
    _ ≤ (gN s * ((2 * r + k + 1 : ℕ) : ℝ)) * gN s := by gcongr
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * gN s ^ 2 := by ring
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
