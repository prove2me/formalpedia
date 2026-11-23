-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.IsUB.det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:59.318924+00:00
-- url     : https://prove2.me/submissions/73a229f6-5928-4c32-9b56-ac17daeb61f4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_zero_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}
namespace Formalism.L2.S.L6.UnitaryStandardVectors
namespace IsUB
theorem _root_.solution {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : C.det = 1 := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  rw [Matrix.det_of_upperTriangular hup]
  exact Finset.prod_eq_one fun i _ => h.1 i
end IsUB
end Formalism.L2.S.L6.UnitaryStandardVectors
