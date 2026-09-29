-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.N_eq_of_le_of_mem_stratum_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1fcd676a-e118-5910-a07b-16c2b83b40b4

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N0_eq_of_not_mem_stratum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N_eq_of_le_of_mem_stratum_iff

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (x' : PrimeSpectrum B')
    (h₀ : Q.N₀ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₀ x')
    (h₁ : Q.N₁ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₁ x')
    (hs₀ : x' ∈ Q'.stratum₀ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₀)
    (hs₁ : x' ∈ Q'.stratum₁ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₁)
    (hcov : x' ∈ Q'.stratum₀ ∨ x' ∈ Q'.stratum₁) :
    Q'.N₀ x' = Q.N₀ (DrinfeldDatum.pointUnder f x') ∧ Q'.N₁ x' = Q.N₁ (DrinfeldDatum.pointUnder f x') := by
  set x := DrinfeldDatum.pointUnder f x' with hx
  have hp0 : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) ≠ 0 := by
    rw [map_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective (fun v : Fin 2 → ℚ_[p] => algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v) :=
    smul_right_injective (Fin 2 → ℚ_[p]) hp0
  have BQ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.N0_eq_of_not_mem_stratum p Q x
  have BQ' := CerednikDrinfeld.FormalOmega.DrinfeldDatum.N0_eq_of_not_mem_stratum p Q' x'

  have E0 : x' ∈ Q'.stratum₀ → Q'.N₀ x' = Q.N₀ x := fun hS0' =>
    (LT.LatticeTree.eq_of_le_of_hasDetIndex_padic p _ _ h₀ 0 (Q.hasDetIndex₀ x (hs₀.mp hS0'))
      (Q'.hasDetIndex₀ x' hS0')).symm
  have E1 : x' ∈ Q'.stratum₁ → Q'.N₁ x' = Q.N₁ x := fun hS1' =>
    (LT.LatticeTree.eq_of_le_of_hasDetIndex_padic p _ _ h₁ (-1) (Q.hasDetIndex₁ x (hs₁.mp hS1'))
      (Q'.hasDetIndex₁ x' hS1')).symm
  by_cases hS0' : x' ∈ Q'.stratum₀
  · by_cases hS1' : x' ∈ Q'.stratum₁
    · exact ⟨E0 hS0', E1 hS1'⟩
    ·
      have hS1 : x ∉ Q.stratum₁ := fun h => hS1' (hs₁.mpr h)
      have e0 := E0 hS0'
      refine ⟨e0, le_antisymm ?_ h₁⟩
      intro v hv'
      have hpv : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ Q.N₀ x := e0 ▸ Q'.smul_le x' v hv'
      obtain ⟨w, hw, hvw⟩ := ((BQ.1 hS1) _).mp hpv
      have : v = w := hinj hvw
      rw [this]; exact hw
  · have hS1' : x' ∈ Q'.stratum₁ := hcov.resolve_left hS0'
    have hS0 : x ∉ Q.stratum₀ := fun h => hS0' (hs₀.mpr h)
    have e1 := E1 hS1'

    refine ⟨?_, e1⟩
    rw [BQ'.2 hS0', BQ.2 hS0, e1]

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N_eq_of_le_of_mem_stratum_iff
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N_eq_of_le_of_mem_stratum_iff (solution)
