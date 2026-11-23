-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.phi_posB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:25.823732+00:00
-- url     : https://prove2.me/submissions/d040498b-0ac8-4b73-968e-4db8a9b86d0b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_frac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0)
    (h : 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1)) : Pos (phiL l Y) := by
  unfold phiL
  unfold ypt at h
  split_ifs at h ⊢
  · have := frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this
  · have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at h ⊢; nlinarith)
    simpa [sub_eq_add_neg] using this
end Formalism.FourierDecayAlt.P.Fr2
