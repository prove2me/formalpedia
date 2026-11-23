-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.isUnit_Z
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:04.445781+00:00
-- url     : https://prove2.me/submissions/fb41c9ee-f0f2-4036-bce0-64493a1132ad

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_Z_mul_Zi

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
variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution : IsUnit Z.det := Matrix.isUnit_det_of_right_inverse (Z_mul_Zi π hπ Z hZ)
end Formalism.L2.S.L6.UnitaryStandardVectors
