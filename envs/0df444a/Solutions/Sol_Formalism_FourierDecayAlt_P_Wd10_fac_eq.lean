-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.fac_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:19.770847+00:00
-- url     : https://prove2.me/submissions/f8d2cb43-6b12-4d7e-bb83-ea47ca14d64f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K S : Type} [Field K]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution (l l' : Letter K S) (hr : RegL l' (dl l).pt) (hg : gq l' (ypt l) ≠ 0) :
    gq l' (ypt l) / hp l' (dl l).pt = fac l l' := by
  obtain ⟨p, s, a⟩ := l
  obtain ⟨p', s', b⟩ := l'
  cases p <;> cases p' <;>
    simp only [gq, hp, fac, ypt, dl, RegL, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hr hg ⊢ <;>
    rw [div_ne_zero_iff] at hg <;> obtain ⟨h1, h2⟩ := hg
  ·
    have e1 : a - 1 - b ≠ 0 := fun h => h1 (by linear_combination -h)
    have e2 : a - 1 - b + 1 ≠ 0 := fun h => h2 (by linear_combination -h)
    field_simp
    ring
  ·
    have e1 : a - 1 - b - 1 ≠ 0 := fun h => hr (by linear_combination h)
    have e3 : a - b + -1 ≠ 0 := fun h => h2 (by linear_combination h)
    field_simp
    ring
  ·
    have e1 : a + 1 - b ≠ 0 := fun h => h2 (by linear_combination -h)
    have e2 : a + 1 - b + 1 ≠ 0 := fun h => hr (by linear_combination -h)
    have e3 : a - b + 1 ≠ 0 := fun h => h2 (by linear_combination -h)
    field_simp
    ring
  ·
    have e1 : a + 1 - b - 1 ≠ 0 := fun h => h2 (by linear_combination h)
    have e2 : a + 1 - b ≠ 0 := fun h => h1 (by linear_combination h)
    field_simp
    ring
end Formalism.FourierDecayAlt.P.Wd10
