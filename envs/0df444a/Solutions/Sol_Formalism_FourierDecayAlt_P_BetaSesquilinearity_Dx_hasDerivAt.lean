-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:21:18.42607+00:00
-- url     : https://prove2.me/submissions/e113a652-b3f7-41e0-ac7f-1f7cf5fa592f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_hasDerivAt
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
theorem _root_.solution {x : Bool × Mat k r} (hx : inLie k r x.2) {f f' : Mat k r → E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (fderiv ℝ f' g (dirv x g)) 0 := by
  have hcomp : HasDerivAt (fun t : ℝ => f' (crv x g t)) (fderiv ℝ f' g (dirv x g)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (crv_hasDerivAt x g) (crv_zero x g).symm
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [crv_ev (x := x) hU hgU] with t ht
  exact hff _ ht (crv_mem hx hg t)
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
