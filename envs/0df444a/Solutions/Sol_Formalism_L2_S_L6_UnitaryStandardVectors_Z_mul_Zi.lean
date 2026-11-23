-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.Z_mul_Zi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:28.325338+00:00
-- url     : https://prove2.me/submissions/49e7f7f4-c4c1-43d2-8bed-3ae64615ec4a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_P2M_Formalism_L2_S_L6_UnitaryStandardVectors_Z_ne__2f739ef805d0

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
theorem _root_.solution : Z * Zi π Z = 1 := by
  ext i k
  simp only [mul_apply, Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, one_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    exact mul_inv_cancel₀ (Z_ne' π hπ Z hZ i)
  · rw [if_neg hik]
    have h0 : Z i (π k) = 0 := by
      by_contra hne
      have h1 := (hZ i (π k)).mp hne
      rw [hπ] at h1
      exact hik h1
    rw [h0, zero_mul]
end Formalism.L2.S.L6.UnitaryStandardVectors
