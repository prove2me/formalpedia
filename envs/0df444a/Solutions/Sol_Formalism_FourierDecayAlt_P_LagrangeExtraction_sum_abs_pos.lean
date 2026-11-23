-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.sum_abs_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:51.49629+00:00
-- url     : https://prove2.me/submissions/ecfd12ce-e621-4bd7-8cac-7383e03ef514

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_lagCo_ne_zero

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
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) :
    0 < ∑ i, |lagCo y i| := Finset.sum_pos' (fun i _ => abs_nonneg _)
    ⟨0, Finset.mem_univ _, abs_pos.mpr (lagCo_ne_zero y hy 0)⟩
end Formalism.FourierDecayAlt.P.LagrangeExtraction
