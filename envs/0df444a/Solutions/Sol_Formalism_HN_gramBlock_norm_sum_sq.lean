-- Prove2me | solution 1 for Formalism.HN.gramBlock_norm_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:25.763292+00:00
-- url     : https://prove2.me/submissions/574c273b-2aa3-40f9-aba2-849cde8a50a8

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {P F : Type*} [Fintype P] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (y : P → F) (h : ∀ v w, v ≠ w → inner ℝ (y v) (y w) = 0) :
    ‖∑ v, y v‖ ^ 2 = ∑ v, ‖y v‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single v (fun w _ hw => h v w (Ne.symm hw)) (by simp),
    real_inner_self_eq_norm_sq]
end Formalism.HN
