-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:54:10.394015+00:00
-- url     : https://prove2.me/submissions/5268816b-5641-4805-8921-d761cd6ed4fe

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_hasDerivAt

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
theorem _root_.solution {x : Bool × Mat k r} (hx : inLie k r x.2) {UU : Set (Mat k r)}
    {f : Mat k r → E} (hf : CkOn 1 UU f) {g : Mat k r} (hgU : g ∈ UU) (hg : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  obtain ⟨U, f', hU, hgU', hc, he⟩ := hf g hgU
  have hd : DifferentiableAt ℝ f' g :=
    (hc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU')
  have h := Dx_hasDerivAt hx hU hgU' hg hd he
  rw [Dx_eq]
  rwa [h.deriv]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
