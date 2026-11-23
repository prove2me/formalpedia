-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.mult_single_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:05.758582+00:00
-- url     : https://prove2.me/submissions/35fac26c-e248-4d53-8ac2-010dad8ef63a

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_eq

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
theorem _root_.solution (l : Letter ℂ S) (γ : ℂ) (b : S) (hb : l.intersection_update_fsHerm_neg_one ≠ b) (i j : Fin 2) :
    (mult [l] γ * eU b i j : SlopeTestRemainingChoices S A) = eU b i j * mult [l] γ := by
  rw [mult_eq]
  refine dg_eU _ b i j ?_
  intro x y hxy
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hxy l.intersection_update_fsHerm_neg_one hb]
end Formalism.FourierDecayAlt.P.Fr11
