-- Prove2me | solution 1 for Formalism.L2.Th1.A.dL_uPow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:21.020615+00:00
-- url     : https://prove2.me/submissions/20c14ec9-3e0e-4adf-802e-fca864c5d1a8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution (n : ℤ) :
    dL (uPow n : LaurentSeries R) = HahnSeries.C ((n : ℤ) : R) * uPow (n - 1) := by
  have h1 : dL (1 : LaurentSeries R) = 0 := by
    have h := dL_toL (R := R) 1
    rwa [map_one, Derivation.map_one_eq_zero, map_zero] at h
  have h := dL_uPow_mul n (1 : LaurentSeries R)
  rw [mul_one, mul_one, h1, mul_zero, zero_add] at h
  exact h
end Formalism.L2.Th1.A
