-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.start_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:27.760878+00:00
-- url     : https://prove2.me/submissions/1e36674e-9a61-49e5-bbc5-de5796601f70

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_freeOf2_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr4
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr4
theorem _root_.solution (st : Start A) (c : S) : (st.frame : FrameData S A).Free c :=
  ⟨free_one c, fun _ => freeOf2_lift c _, free_one c, free_one c, fun _ => free_io c _, fun _ => free_io c _,
    free_one c, free_one c, fun _ => free_io c _⟩
end Formalism.FourierDecayAlt.P.Fr4
