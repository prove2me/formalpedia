-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.ins_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:23.829868+00:00
-- url     : https://prove2.me/submissions/ad811630-4094-4f59-97b6-6837894c6c7d

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
theorem _root_.solution (a : S) (p q s : SlopeTestRemainingChoices S A) :
    ins a !![p, q; 0, s] = eU a 0 0 * p + eU a 0 1 * q + eU a 1 1 * s := by
  simp [ins, Fin.sum_univ_two]
end Formalism.FourierDecayAlt.P.Fr11
