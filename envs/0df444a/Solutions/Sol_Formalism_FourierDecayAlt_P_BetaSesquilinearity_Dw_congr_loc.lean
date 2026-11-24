-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:42:19.045716+00:00
-- url     : https://prove2.me/submissions/cf422fa0-bc67-4814-b5f8-5c61ac9faa5c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr_loc

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
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {O : Set (Mat k r)}
    (hO : IsOpen O) {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, g ∈ O → f g = f₂ g) :
    ∀ g ∈ GV k r, g ∈ O → Dw w f g = Dw w f₂ g := by
  induction w with
  | nil => exact h
  | cons x w ih =>
    intro g hg hgO
    exact Dx_congr_loc (hw x (by simp)) hO (ih (fun y hy => hw y (by simp [hy]))) g hg hgO
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
