-- Prove2me | solution 1 for Formalism.GM.DetBound.norm_inv_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:09.146127+00:00
-- url     : https://prove2.me/submissions/8c7dc820-86ec-4f5b-adfc-09c026a59d72

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_norm_det_le_one

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
theorem _root_.solution {n : ℕ} (U : Matrix (Fin n) (Fin n) K) (hU : ∀ i j, ‖U i j‖ ≤ 1)
    (hdet : ‖U.det‖ = 1) (i j : Fin n) : ‖U⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul, norm_mul, norm_inv, hdet,
    inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs <;> simp
  · exact hU k l
end Formalism.GM.DetBound
