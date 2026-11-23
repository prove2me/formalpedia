-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.blk_eta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:27.662953+00:00
-- url     : https://prove2.me/submissions/805044cb-653c-45ac-870b-4528800e187b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_mat_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    M = blk (Matrix.of fun i j => M i.castSucc j.castSucc) (fun i => M i.castSucc (Fin.last n))
      (fun j => M (Fin.last n) j.castSucc) (M (Fin.last n) (Fin.last n)) :=
  mat_ext (fun i j => by rw [blk_cc]; rfl) (fun i => by rw [blk_cl]) (fun j => by rw [blk_lc])
    (by rw [blk_ll])
end Formalism.FourierDecayAlt.P.G4
