-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_congr_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:21:20.736796+00:00
-- url     : https://prove2.me/submissions/a94d83b5-1ce7-49df-a1ae-815177efbaef

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_ev

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
theorem _root_.solution {x : Bool × Mat k r} (hx : inLie k r x.2) {O : Set (Mat k r)} (hO : IsOpen O)
    {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, g ∈ O → f g = f₂ g) :
    ∀ g ∈ GV k r, g ∈ O → Dx x f g = Dx x f₂ g := by
  intro g hg hgO
  rw [Dx_eq, Dx_eq]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [crv_ev (x := x) hO hgO] with t ht
  exact h _ (crv_mem hx hg t) ht
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
