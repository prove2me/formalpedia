-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.character_modulus_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:30.236345+00:00
-- url     : https://prove2.me/submissions/011a2877-f817-49d5-8097-7f9a2b625d07

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_character_power_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : ChiModulusAll := by
  intro E _ _ Ψ A _ ι K χ hcm hK hχ t h z k hh hk ht s
  have e := character_power_formula E Ψ A ι K χ hK hχ t h z k hk ht
  have u : ∀ τ : E →+* ℂ, ‖s (τ (z : E))‖ = 1 := by
    intro τ
    have h1 : star (z : E) * (z : E) = 1 := (Unitary.mem_iff.1 z.2).1
    have h2 := congrArg (s.comp τ) h1
    rw [map_mul, map_one, hcm (s.comp τ)] at h2
    have h3 := congrArg (fun w : ℂ => ‖w‖) h2
    simp only [norm_mul, RCLike.norm_conj, norm_one, RingHom.comp_apply] at h3
    nlinarith [norm_nonneg (s (τ (z : E)))]
  have p : ‖s ((χ t : Circle) : ℂ)‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, e, map_prod, norm_prod]
    apply Finset.prod_eq_one
    intro τ _
    rw [map_inv₀, norm_inv, u, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 p
end Formalism.HermitianLattices.ModelCocycles
