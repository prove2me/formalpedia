-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:47:22.354795+00:00
-- url     : https://prove2.me/submissions/16b50711-117a-45c3-98a7-688689f8e67a

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {u v : List (Mat k r)} (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, inLie k r X) :
    ∀ x ∈ wL u ++ wR v, inLie k r x.2 := by
  intro x hx
  simp only [wL, wR, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
