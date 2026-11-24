-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:54:47.85254+00:00
-- url     : https://prove2.me/submissions/e28eb1ca-5099-4785-bb95-597677432c20

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_vanish

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
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {O : Set (Mat k r)} (hO : IsOpen O) {v : List (Mat k r)} (hv : ∀ X ∈ v, inLie k r X)
    {f : Mat k r → E} (hz : ∀ g ∈ GV k r, g ∈ O → f g = 0) : ∀ g ∈ GV k r, g ∈ O → Rw v f g = 0 := by
  rw [← Dw_wR]
  refine Dw_vanish hO (fun x hx => ?_) hz
  simp only [wR, List.mem_map] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  exact hv X hX
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
