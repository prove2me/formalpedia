-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.word_le_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:23:03.424848+00:00
-- url     : https://prove2.me/submissions/06ac28cb-a05b-4517-a174-8d2086a419e1

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (Θ : DiffOp k r Wp Wq) {T : DTerm k r Wp Wq} (hT : T ∈ Θ) :
    T.word.length ≤ opOrder Θ := by
  induction Θ with
  | nil => simp at hT
  | cons T' Θ ih =>
    show T.word.length ≤ max T'.word.length ((Θ.map fun T => T.word.length).foldr max 0)
    rcases List.mem_cons.mp hT with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
