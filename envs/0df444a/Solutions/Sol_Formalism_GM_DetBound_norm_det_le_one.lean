-- Prove2me | solution 1 for Formalism.GM.DetBound.norm_det_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:51.069014+00:00
-- url     : https://prove2.me/submissions/a60888bd-4d48-4bae-91d5-4f3ee803cad5

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_C
import Theorems.Thm_Formalism_GM_DetBound_gaussR_det_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.GM.DetBound
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  have h := gaussR_det_le 1 (M.map C) (fun _ => 1) (fun i j => by
    rw [Matrix.map_apply, gaussR_C, ← NNReal.coe_le_coe]; simpa using hM i j)
  have e : (M.map C).det = C M.det := (RingHom.map_det C M).symm
  rw [e, gaussR_C, prod_const_one, ← NNReal.coe_le_coe] at h
  simpa using h
end Formalism.GM.DetBound
