-- Prove2me | solution 1 for FormalGroup.IsBaseChange.exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fe2fe720-6638-5899-88a8-d499c1f28197

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_PowerSeries_exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) (k : Type) [Field k]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀))
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀) :
    ∃ (P : Polynomial (PowerSeries W₀)) (U : PowerSeries (PowerSeries W₀)),
      P.Monic ∧ P.natDegree = q * q ∧
      (∀ i : ℕ, i < q * q → P.coeff i ∈ maximalIdeal (PowerSeries W₀)) ∧
      IsUnit U ∧ Fu.nthSeries q = (P : PowerSeries (PowerSeries W₀)) * U := by
  classical

  haveI : IsAdicComplete (maximalIdeal (PowerSeries W₀)) (PowerSeries W₀) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := W₀)

  haveI : IsAdicComplete (⊥ : Ideal k) k := inferInstance

  obtain ⟨u, hu, hq⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) F₀ q).mp hF₀

  let θ : PowerSeries W₀ →+* k := res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)
  have hmap : F₀.nthSeries q = PowerSeries.map θ (Fu.nthSeries q) :=
    FormalGroup.IsBaseChange.nthSeries_eq_map Fu θ F₀ hFu q
  have hθ : ∀ a : PowerSeries W₀, θ a = 0 ↔ a ∈ maximalIdeal (PowerSeries W₀) := by
    intro a
    show res₀ (PowerSeries.constantCoeff a) = 0 ↔ _
    rw [← RingHom.mem_ker, hker₀, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  exact PowerSeries.exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow θ hθ (Fu.nthSeries q) (q * q) u hu (by rw [← hmap, hq])

end S_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
end P2MW
export P2MW.S_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul (solution)
