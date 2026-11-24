-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.thr_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:10:11.798193+00:00
-- url     : https://prove2.me/submissions/ee598032-a9a7-4b84-8534-fea622635364

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {k r : ℕ} {A : ℝ} {m : ℕ} (h : TransportedAlt k r A m) :
    0 < Ap r A m ∧ B.AB k r ≤ Ap r A m ∧ 0 < A - 6 * (r : ℝ) * m ∧
    (5 * (r : ℝ) + 1) * Ap r A m ≤ A - 6 * (r : ℝ) * m := by
  unfold TransportedAlt at h
  have hr : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hAp : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < Ap r A m := h
  have hAB : B.AB k r ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
    unfold B.AB; push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hpos : 0 < Ap r A m := lt_of_le_of_lt hn hAp
  have heq : A - 6 * (r : ℝ) * m = 9 * ((r : ℝ) + 1) * Ap r A m := by
    unfold Ap; field_simp
  refine ⟨hpos, hAB.trans hAp.le, by rw [heq]; positivity, ?_⟩
  rw [heq]; nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
end Formalism.FourierDecayAlt.P.SliceLastLevel
