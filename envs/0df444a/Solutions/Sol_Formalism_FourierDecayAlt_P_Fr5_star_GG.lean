-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.star_GG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:53.414813+00:00
-- url     : https://prove2.me/submissions/f2bedc69-58ff-4b1f-a205-c9dcda53fd01

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__b_9c3419007fcb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star L.GG = L.GG := by
  have h' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := h
  have e : star (L.ζ * L.ζb) = L.ζ * L.ζb := by rw [star_mul, star_ζb h, h'.1]
  rw [L.GG_def, star_sub, e]
  first
  | rw [← algebraMap_star_comm, h'.2.2]
  | rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, h'.2.2]
end Formalism.FourierDecayAlt.P.Fr5
