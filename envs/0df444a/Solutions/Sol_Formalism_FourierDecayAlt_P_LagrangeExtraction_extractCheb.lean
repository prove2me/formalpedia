-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.extractCheb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:16.768902+00:00
-- url     : https://prove2.me/submissions/8f129a6b-929a-41c0-b3b7-177a258cdfe3

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_extractBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_sharp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LagrangeExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction
theorem _root_.solution : ExtractCheb := by
  intro V _ _ K d s W α β hd hαβ hP y₀ B hB
  have h := extractBound V K d s W (fun a => Formalism.SA.C.chebPt (α a) (β a) d) hP
    (fun a => (ChebyshevExtremalPolynomials.sharp (α a) (β a) d (hαβ a) hd).1) y₀ B hB
  have e : (∏ a, ∑ i, |lagCo (Formalism.SA.C.chebPt (α a) (β a) d) i|) =
      ∏ a, (1 / 2) * (4 / (β a - α a)) ^ d :=
    Finset.prod_congr rfl fun a _ => (ChebyshevExtremalPolynomials.sharp (α a) (β a) d (hαβ a) hd).2
  rw [← e]
  exact h
end Formalism.FourierDecayAlt.P.LagrangeExtraction
