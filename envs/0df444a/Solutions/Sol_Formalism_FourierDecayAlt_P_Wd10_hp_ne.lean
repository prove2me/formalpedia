-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.hp_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:20.753361+00:00
-- url     : https://prove2.me/submissions/3493f14f-d96f-4832-8527-fe2936c3b63d

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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution {l : Letter K S} {Y : K} (h1 : RegL l Y) (h2 : RegL (dl l) Y) : hp l Y ≠ 0 := by
  obtain ⟨p, s, a⟩ := l
  cases p <;> simp only [hp, dl, RegL, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
  · exact div_ne_zero (fun h => h2 (by linear_combination h)) (fun h => h1 (by linear_combination -h))
  · exact div_ne_zero (fun h => h2 (by linear_combination -h)) (fun h => h1 (by linear_combination h))
end Formalism.FourierDecayAlt.P.Wd10
