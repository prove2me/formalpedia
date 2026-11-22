-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.mult_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:28.055817+00:00
-- url     : https://prove2.me/submissions/6ee5a2e2-9444-466d-a0dd-a000b44fd187

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (v : List (Letter ℂ S)) (γ : ℂ) :
    (mult v γ : SlopeTestRemainingChoices S A) = dg fun e => (v.map fun l => 1 + sg (e l.intersection_update_fsHerm_neg_one) / (l.pt - γ)).prod := rfl
end Formalism.FourierDecayAlt.P.Fr11
