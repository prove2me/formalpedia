-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.not_cm_eq_of_conj_smul_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:36.572113+00:00
-- url     : https://prove2.me/submissions/74f5bbf6-4cd9-4405-98c6-409f7714626d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_stab_Psi
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cc_not_mem
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_galE_restrict_mem_Psi
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_inv
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois
import Theorems.Thm_Formalism_Q3_cc_not_mem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ)
    (hr : r = 2 ∨ r = q) (𝔭 : Ideal (𝓞 (KinE ζ a b)))
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P)
    (h1 : cm P = 𝔭) (h2 : cm (c • P) = 𝔭) : False := by
  have hqd := hH.toHypOdd
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have hKgal : IsGalois (KinE ζ a b) (hostE ζ a b) := IsGalois.tower_top_of_isGalois ℚ _ _
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) (𝓞 (KinE ζ a b))
      (𝓞 (hostE ζ a b)) := IsGaloisGroup.of_isFractionRing _ _ _ (KinE ζ a b) (hostE ζ a b)
  have l1 : P.LiesOver 𝔭 := ⟨h1.symm⟩
  have l2 : (c • P).LiesOver 𝔭 := ⟨h2.symm⟩
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isGaloisGroup 𝔭 P (c • P)
    (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
  have hτ' : (τ.restrictScalars ℚ) • P = c • P := hτ
  have hfix : ((τ.restrictScalars ℚ)⁻¹ * c) • P = P := by
    rw [mul_smul, ← hτ', inv_smul_smul]
  have hmem := stab_Psi hH h r hr P hm _ hfix
  rw [galE_mul hqd h, galE_inv hqd h, hc] at hmem
  have hτΨ := Principal.galE_restrict_mem_Psi (e := e) τ
  have := (Psi e).mul_mem hτΨ hmem
  rw [mul_inv_cancel_left] at this
  exact cc_not_mem e this
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
