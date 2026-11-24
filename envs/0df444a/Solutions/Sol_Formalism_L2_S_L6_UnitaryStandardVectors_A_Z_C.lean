-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.A_Z_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:17.702212+00:00
-- url     : https://prove2.me/submissions/e5fbf575-3fb2-46b5-8be5-46468faeb683

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_det_eq_one
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_isUnit_Z

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
variable {blk : Fin m → ℕ} (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a)
  (hanti : ∀ a b, blk a = blk b → a < b → π b < π a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hblk hanti hZ
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : (Z * C⁻¹ * Z⁻¹)ᴴᴴ * Z * C = Z := by
  rw [conjTranspose_conjTranspose]
  have hZu := isUnit_Z π hπ Z hZ
  have hCu : IsUnit C.det := by
    rw [hC.det_eq_one]
    exact isUnit_one
  rw [mul_assoc (Z * C⁻¹) Z⁻¹ Z, Matrix.nonsing_inv_mul _ hZu, mul_one, mul_assoc,
    Matrix.nonsing_inv_mul _ hCu, mul_one]
end Formalism.L2.S.L6.UnitaryStandardVectors
