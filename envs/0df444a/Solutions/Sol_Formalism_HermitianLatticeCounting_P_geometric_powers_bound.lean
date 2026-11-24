-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.geometric_powers_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:50.917822+00:00
-- url     : https://prove2.me/submissions/ad2f8308-7b3c-4e58-bdec-21928d15858b

import Definitions.Def_Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_GaussSumCharacterAverageBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_geo_q
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S4 Formalism.HermitianLatticeCounting.P.S4aux Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.GeomPowers := by
  intro q k N hq hk
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hx : (2 : ℝ) ≤ (q : ℝ) ^ (k - 1) := by
    calc (2 : ℝ) ≤ q := hq2
      _ = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have e : ∀ i : ℕ, ((q : ℝ) ^ i) ^ (k - 1) = ((q : ℝ) ^ (k - 1)) ^ i := fun i => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [e]
  have := geo_q _ hx N
  linarith
end Formalism.HermitianLatticeCounting.P
