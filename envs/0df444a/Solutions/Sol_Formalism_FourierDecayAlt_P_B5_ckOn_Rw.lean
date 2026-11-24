-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.ckOn_Rw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:20.670249+00:00
-- url     : https://prove2.me/submissions/c1926a86-0dab-47d8-a8e7-598228f13fb2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_RdV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {f : Mat k r → E} {N : ℕ} (h : CkOn (N : ℕ∞) (GV k r) f) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) : CkOn (m : ℕ∞) (GV k r) (Rw w f) := by
  induction w generalizing m with
  | nil =>
    have hmN : m ≤ N := by simpa using hle
    exact ckOn_mono (by exact_mod_cast hmN) h
  | cons X w ih =>
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (by simp [hY])
    have hle' : m + 1 + w.length ≤ N := by simp at hle; omega
    have h1 : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) (Rw w f) := ih hw' (m + 1) hle'
    push_cast at h1
    exact ckOn_RdV hX h1
end Formalism.FourierDecayAlt.P.B5
