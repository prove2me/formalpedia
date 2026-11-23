-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Ph_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:51.016113+00:00
-- url     : https://prove2.me/submissions/aacc2ce6-d00b-456d-a315-e39b449920ef

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_zero

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
variable {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ)
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution {J : Type} (s : Finset J) (U V : J → B) :
    Ph p0 p1 c (∑ j ∈ s, U j) (∑ j ∈ s, V j) = ∑ j ∈ s, Ph p0 p1 c (U j) (V j) := by
  induction s using Finset.cons_induction with
  | empty => simp [Ph_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, Ph_add, ih]
end Formalism.FourierDecayAlt.P.Fr11
