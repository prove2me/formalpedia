-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.num_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:03.985701+00:00
-- url     : https://prove2.me/submissions/f611c23a-071d-44fb-a612-cb3af1fb52b3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π π') :
    I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) = 0 := by
  have hl' := Finset.mem_Icc.1 hl
  have ht := top P hP l hl π h
  unfold I.qpoly
  have : ∏ i ∈ Icc 1 P.k, ((-rho P π l - 1 + 1 / 2 + P.u i) * (-rho P π l - 1 + 1 / 2 + P.u' i)) = 0 := by
    apply Finset.prod_eq_zero (i := l) (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
    rw [ht]; unfold Par.hi
    rcases min_choice (P.u l) (P.u' l) with h | h <;> rw [h] <;> ring
  rw [this]; simp
end Formalism.FourierDecayAlt.P.Mx3
