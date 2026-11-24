-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.sum_eU_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:29.484422+00:00
-- url     : https://prove2.me/submissions/498de721-37aa-468a-ab4c-7d4bc2f0e0c9

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution (a : S) : ∑ i, (eU a i i : SlopeTestRemainingChoices S A) = 1 := by
  ext x y
  rw [Matrix.sum_apply, Finset.sum_eq_single (x a)]
  · rw [eU_apply, Matrix.one_apply, Function.update_eq_self]
    by_cases h : x = y
    · subst h; simp
    · have h' : ¬ y = x := fun e => h e.symm
      simp [h, h']
  · intro i _ hi
    rw [eU_apply, if_neg]
    rintro ⟨h, _⟩
    exact hi h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Wd1
