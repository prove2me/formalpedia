-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.real_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:46:20.453811+00:00
-- url     : https://prove2.me/submissions/1f54fe1b-4b39-4507-8d30-ac4b24d3f6f2

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_rp_bd

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
theorem _root_.solution (X G1 G2 C4 Λ1 A A1 β P : ℝ) (m r : ℕ) (hX : 1 ≤ X) (hC4 : 1 ≤ C4) (hG1 : 1 ≤ G1)
    (hG2 : 1 ≤ G2) (h1 : G1 ≤ C4 * X ^ (3 * r)) (h2 : G2 ≤ C4 * X ^ (3 * r)) (hβ : 0 ≤ β)
    (hβA : 6 * (r : ℝ) * β ≤ A1) (hA1 : A1 = A - 6 * (r : ℝ) * (m : ℝ)) (hΛ : 1 ≤ Λ1)
    (hP : P ≤ (Λ1 * X ^ (6 * r)) ^ m) :
    P * X ^ (-A) ≤ Λ1 ^ m * (C4 ^ β) ^ 2 * (G1 ^ (-β) * G2 ^ (-β)) := by
  have hXpos : 0 < X := by linarith
  have hXA : 0 ≤ X ^ (-A) := Real.rpow_nonneg hXpos.le _
  have hb1 := rp_bd X C4 G1 β (3 * r) (by linarith) (by linarith) h1 hβ
  have hb2 := rp_bd X C4 G2 β (3 * r) (by linarith) (by linarith) h2 hβ
  have hn1 : 0 ≤ (X ^ (3 * r)) ^ (-β) := Real.rpow_nonneg (by positivity) _
  have hn2 : 0 ≤ C4 ^ β * G1 ^ (-β) := by
    have := Real.rpow_nonneg (show (0:ℝ) ≤ C4 by linarith) β
    have := Real.rpow_nonneg (show (0:ℝ) ≤ G1 by linarith) (-β); positivity
  have hΛm : 0 ≤ Λ1 ^ m := by positivity
  calc P * X ^ (-A) ≤ (Λ1 * X ^ (6 * r)) ^ m * X ^ (-A) := mul_le_mul_of_nonneg_right hP hXA
    _ = Λ1 ^ m * X ^ (-A1) := by
        rw [mul_pow, ← pow_mul, mul_assoc, ← Real.rpow_natCast X (6 * r * m), ← Real.rpow_add hXpos]
        congr 2
        rw [hA1]; push_cast; ring
    _ ≤ Λ1 ^ m * X ^ (-(6 * (r : ℝ) * β)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hΛm
    _ = Λ1 ^ m * ((X ^ (3 * r)) ^ (-β) * (X ^ (3 * r)) ^ (-β)) := by
        congr 1
        rw [← Real.rpow_natCast X (3 * r), ← Real.rpow_mul hXpos.le, ← Real.rpow_add hXpos]
        congr 1; push_cast; ring
    _ ≤ Λ1 ^ m * ((C4 ^ β * G1 ^ (-β)) * (C4 ^ β * G2 ^ (-β))) := by
        gcongr
    _ = Λ1 ^ m * (C4 ^ β) ^ 2 * (G1 ^ (-β) * G2 ^ (-β)) := by ring
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
