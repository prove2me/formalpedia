-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.top_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:56.236453+00:00
-- url     : https://prove2.me/submissions/0c240df2-22fe-46a4-82ca-ec889da79be1

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_top_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hC : ∀ c d (f f₂ : Mat k r → E), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop c d f g = Eop c d f₂ g)
    (u : ℂ) (c d : Fin (2 * r + k + 1)) {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, f g = f₂ g) :
    ∀ g ∈ GV k r, Top Eop u c d f g = Top Eop u c d f₂ g := by
  intro g hg
  rw [top_apply, top_apply, h g hg, hC c d f f₂ h g hg]
end Formalism.FourierDecayAlt.P.JFxB
