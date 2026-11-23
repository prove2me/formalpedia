-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.star_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:07.157835+00:00
-- url     : https://prove2.me/submissions/dd9f0ea8-37df-41af-bf07-ede5390768e4

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_fn_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem___d82dc59c5260
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__b_4a242cf5d7ab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_mem_GGi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__b_9c3419007fcb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_star_GGi

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
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  have h' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := h
  have k1 : Commute L.GGi L.ζ := fn_comm L (mem_GGi L) (mem_ζ L)
  have k2 : Commute L.GGi L.ζb := fn_comm L (mem_GGi L) (mem_ζb L)
  show star (io (L.ζ * L.ζb * L.GGi) : SlopeTestRemainingChoices S A) = io (L.ζ * L.ζb * L.GGi)
  rw [io_star, star_mul, star_mul, star_GGi h, star_ζb h, h'.1]
  congr 1
  exact (k1.mul_right k2).eq
end Formalism.FourierDecayAlt.P.Fr5
