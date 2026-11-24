-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:02.813551+00:00
-- url     : https://prove2.me/submissions/341b5308-1c9d-4263-838f-611bbe1864b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_Z_inv_eq

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
theorem _root_.solution (X : Matrix (Fin m) (Fin m) ℂ) (j i : Fin m) :
    (Z * X * Z⁻¹) j i = Z j (π j) * X (π j) (π i) * (Z i (π i))⁻¹ := by
  rw [Z_inv_eq π hπ Z hZ]
  simp only [mul_apply, Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_eq_single (π j)]
  · intro l _ hl
    have h0 : Z j l = 0 := by
      by_contra hne
      apply hl
      rw [(hZ j l).mp hne, hπ]
    rw [h0, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ _) hj
end Formalism.L2.S.L6.UnitaryStandardVectors
