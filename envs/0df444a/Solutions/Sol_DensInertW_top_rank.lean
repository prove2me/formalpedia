-- Prove2me | solution 1 for DensInertW.top_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:15.258569+00:00
-- url     : https://prove2.me/submissions/16c7993f-fcfe-41e3-a6ea-b24baf20d870

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (m : ℕ) (B P : Matrix (Fin m) (Fin m) L) (hP : IsUnit P.det) :
    (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose).rank = B.rank := by
  have hF : P.map (fun y => y ^ Fintype.card K) =
      P.map ((FiniteField.frobeniusAlgHom K L : L →ₐ[K] L) : L →+* L) := by
    ext i j
    simp [FiniteField.frobeniusAlgHom_apply]
  have hu : IsUnit (P.map (fun y => y ^ Fintype.card K)).transpose.det := by
    rw [Matrix.det_transpose, hF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hP.map _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]
end DensInertW
