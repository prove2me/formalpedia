-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.normalised_equation_general
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:41.646279+00:00
-- url     : https://prove2.me/submissions/5be2513c-ce51-4bb8-b9fc-5b90c5171308

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : EqNormalisedGeneral := by
  unfold EqNormalisedGeneral
  intro E _ _ Ψ A _ ι χ G G' Γ Γ' _ _ _ _ j j' dt dt' dr dr' V _ _ pull Th M M' hj hj' hχ hpull
    a b γ γ' g g'
  have hinv : ∀ u : unitary E, ∏ τ ∈ Ψ, τ (star (u : E)) = (∏ τ ∈ Ψ, τ (u : E))⁻¹ := by
    intro u
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Unitary.coe_star_mul_self u, map_one]
  have hne : ∀ u : unitary E, (∏ τ ∈ Ψ, τ (u : E)) ≠ 0 := by
    intro u
    rw [Finset.prod_ne_zero_iff]
    intro τ _ h
    have := congrArg τ (Unitary.coe_star_mul_self u)
    rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  have hχg : ((χ (dt (j γ)) : ℂˣ) : ℂ) = (∏ τ ∈ Ψ, τ ((dr γ : unitary E) : E))⁻¹ := by
    rw [hj, hχ, Finset.prod_inv_distrib]
  have hχg' : ((χ (dt' (j' γ')) : ℂˣ) : ℂ) = (∏ τ ∈ Ψ, τ ((dr' γ' : unitary E) : E))⁻¹ := by
    rw [hj', hχ, Finset.prod_inv_distrib]
  have hP := hne (dr γ)
  have hP' := hne (dr' γ')
  rw [LinearMap.map_smul, hpull, smul_smul, smul_smul]
  congr 1
  simp only [map_mul, Units.val_mul, Units.val_zpow_eq_zpow_val, mul_zpow, hχg, hχg', hinv]
  generalize (∏ τ ∈ Ψ, τ ((dr γ : unitary E) : E)) = P at hP ⊢
  generalize (∏ τ ∈ Ψ, τ ((dr' γ' : unitary E) : E)) = P' at hP' ⊢
  rw [zpow_sub₀ hP, zpow_add₀ hP', zpow_natCast, zpow_natCast, inv_zpow, inv_zpow, inv_pow]
  field_simp
end Formalism.HermitianLattices.IntegralLatticeDensity
