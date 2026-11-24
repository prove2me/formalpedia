-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.atLeast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:46:28.735372+00:00
-- url     : https://prove2.me/submissions/114f666e-8e4b-41e7-b1c9-482fbe3b47d0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cm_smul
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_int_mem_of_cm
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_liesOver_span_of_natCast_mem_frobenius_orbits
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open NumberField IntermediateField Ideal
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
theorem _root_.solution (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ) (hr : r.Prime)
    (𝔭 : Ideal (𝓞 (KinE ζ a b))) [𝔭.IsPrime] (hm𝔭 : ((r : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm P = 𝔭 ∨ cm (c • P) = 𝔭 := by
  have hqd := hH.toHypOdd
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) ℤ (𝓞 (hostE ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)
  obtain ⟨P₀, -, hP₀, hcm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭
    (⊥ : Ideal (𝓞 (hostE ζ a b))) (by simp [← RingHom.ker_eq_comap_bot])
  have hm₀ := int_mem_of_cm P₀ 𝔭 hcm r hm𝔭
  have l0 : P₀.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P₀ r hr hm₀
  have l1 : P.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P r hr hm
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup (span {(r : ℤ)}) P₀ P
    (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
  by_cases hΨ : galE e ζ a b σ ∈ Psi e
  · left
    rw [← hσ, cm_smul hqd h σ hΨ]; exact hcm
  · right
    rw [← hσ, ← mul_smul, cm_smul hqd h (c * σ) ?_]
    · exact hcm
    rw [galE_mul hqd h, hc, mem_Psi_iff]
    rw [mem_Psi_iff] at hΨ
    rcases Int.units_eq_one_or (galE e ζ a b σ).1.2 with h1 | h1
    · exact absurd h1 hΨ
    · simp [cc, c0, h1]
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
