-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.sub_LR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:32:26.316484+00:00
-- url     : https://prove2.me/submissions/6fbd7686-8674-408f-85a8-2c93c349a865

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
theorem _root_.solution {u v : List (Mat k r)} {w : List (Bool × Mat k r)} (h : w.Sublist (wL u ++ wR v)) :
    ∃ u₁ v₁, u₁.Sublist u ∧ v₁.Sublist v ∧ w = wL u₁ ++ wR v₁ := by
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  obtain ⟨u₁, hu₁, rfl⟩ := List.sublist_map_iff.mp h₁
  obtain ⟨v₁, hv₁, rfl⟩ := List.sublist_map_iff.mp h₂
  exact ⟨u₁, v₁, hu₁, hv₁, rfl⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
