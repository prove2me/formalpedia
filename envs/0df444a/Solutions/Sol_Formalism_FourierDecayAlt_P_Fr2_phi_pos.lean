-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.phi_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:25.784691+00:00
-- url     : https://prove2.me/submissions/459fc23e-0317-4f2b-80b4-bf15618a5ede

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_frac
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_gt1

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
theorem _root_.solution (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0) (h : 1 < |Y.re - l.pt.re|) :
    Pos (phiL l Y) := by
  obtain ⟨g1, g2⟩ := gt1 h
  unfold phiL
  split_ifs
  · have := frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this
  · have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this
end Formalism.FourierDecayAlt.P.Fr2
