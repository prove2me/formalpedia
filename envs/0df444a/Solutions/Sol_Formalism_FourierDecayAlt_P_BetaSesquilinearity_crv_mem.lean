-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:52.073492+00:00
-- url     : https://prove2.me/submissions/ede0cfca-c595-456d-a04c-3985631e78e7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_neg

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
theorem _root_.solution {x : Bool × Mat k r} (hx : inLie k r x.2) {g : Mat k r} (hg : g ∈ GV k r) (t : ℝ) :
    crv x g t ∈ GV k r := by
  rcases x with ⟨_ | _, X⟩
  · exact gv_mul hg (exp_mem (lie_rsmul hx t))
  · exact gv_mul (exp_mem (lie_neg (lie_rsmul hx t))) hg
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
