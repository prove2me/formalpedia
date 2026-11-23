-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.blk_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:40.015602+00:00
-- url     : https://prove2.me/submissions/199b245b-9bd0-457d-a7bc-55f5ab287543

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    (blk A b a e)ᵀ = blk Aᵀ a b e :=
  mat_ext (fun i j => by rw [transpose_apply, blk_cc, blk_cc, transpose_apply])
    (fun i => by rw [transpose_apply, blk_lc, blk_cl])
    (fun j => by rw [transpose_apply, blk_cl, blk_lc])
    (by rw [transpose_apply, blk_ll, blk_ll])
end Formalism.FourierDecayAlt.P.G4
