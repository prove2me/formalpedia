-- Prove2me | solution 1 for FrobeniusDensity.chebotarev_natural_density
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-23T19:30:46.546146+00:00
-- url     : https://prove2.me/submissions/81fbd535-ce82-41ea-8a4b-e18b071540b8

import Definitions.Def_LanglandsTunnell_TowerCounting
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_FrobeniusDensity_chebotarev_natural_density_core

set_option autoImplicit false

open NumberField Ideal Filter Topology

/-- Chebotarev's density theorem over `ℚ`, stated as natural density relative to the
rational primes and allowing an arbitrary finite set of excluded residue characteristics. -/
theorem solution
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun ℓ =>
            ℓ ∉ S ∧ LanglandsTunnell.classIndicator σ ℓ = 1).card : ℝ) /
          (((Finset.range X).filter Nat.Prime).card : ℝ))
      atTop
      (𝓝 ((Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) /
        (Nat.card (L ≃ₐ[ℚ] L) : ℝ))) := by
  exact FrobeniusDensity.chebotarev_natural_density_core L σ S
