-- Prove2me | solution 1 for CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/521678e4-59d5-5bdd-b5d5-c24631272cac

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma ℓ ∧ δ ∈ CongruenceSubgroup.Gamma0 M' ∧
      γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma q ∧ δ⁻¹ * γ ∈ CongruenceSubgroup.Gamma q := by
  classical
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  haveI : NeZero (ℓ * M') := ⟨mul_ne_zero hℓp.ne_zero (NeZero.ne M')⟩
  have hcop : Nat.Coprime q (ℓ * M') := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (Nat.coprime_primes hqp hℓp).mpr (Ne.symm hℓq)
    · exact (Nat.Prime.coprime_iff_not_dvd hqp).mpr hqM'
  obtain ⟨δ, hδq, hδℓ⟩ := Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime q (ℓ * M') hcop
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ) 1

  have hent : ∀ i k : Fin 2, (((δ i k : ℤ)) : ZMod (ℓ * M')) = ((1 : SL(2, ZMod (ℓ * M'))) i k) := by
    intro i k
    have := congrArg (fun g : SL(2, ZMod (ℓ * M')) => (g i k)) hδℓ
    simpa [Matrix.SpecialLinearGroup.map] using this
  have hcast : ∀ (n : ℕ) (hn : n ∣ ℓ * M') (i k : Fin 2),
      (((δ i k : ℤ)) : ZMod n) = ZMod.castHom hn (ZMod n) (((1 : SL(2, ZMod (ℓ * M'))) i k)) := by
    intro n hn i k
    rw [← hent, map_intCast]
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  ·
    rw [CongruenceSubgroup.Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hcast ℓ (dvd_mul_right ℓ M')]
        simp
  ·
    rw [CongruenceSubgroup.Gamma0_mem, hcast M' (dvd_mul_left M' ℓ)]
    simp
  · rw [CongruenceSubgroup.Gamma_mem']
    rw [map_mul, map_inv, hδq, mul_inv_cancel]
  · rw [CongruenceSubgroup.Gamma_mem']
    rw [map_mul, map_inv, hδq, inv_mul_cancel]

end S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
end P2MW
export P2MW.S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd (solution)
