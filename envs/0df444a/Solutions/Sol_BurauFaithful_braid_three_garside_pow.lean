-- Prove2me | solution 1 for BurauFaithful.braid_three_garside_pow
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T15:54:49.446988+00:00
-- url     : https://prove2.me/submissions/931d79f4-a8df-4e03-b3a6-ddb0a44adabe

/-
Group-theoretic input for `BurauFaithful.burau_three_spec_kernel`: in `B₃` the square of the
Garside element is the full twist, `Δ² = (σ₁σ₂)³`, hence `Δ⁴ = (σ₁σ₂)⁶`. This is what identifies
the Coxeter relation `(s₁s₂s₁)⁴ = 1` of the modular group with the kernel generator
`(σ₁σ₂)⁶` (Birman, §3.3, Theorem 3.15, pp. 129--130).
-/
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

open BraidsLinksMCG

theorem solution :
    (BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩ * BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩ *
        BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩) ^ 4 =
      (BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩) ^ 6 := by
  -- the braid relation, as an equation in `B₃`
  have hmem : FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * FreeGroup.of 0 *
      (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹ ∈
      Subgroup.normalClosure (BraidsLinksMCG.braidRels 3) :=
    Subgroup.subset_normalClosure (by
      rw [BraidsLinksMCG.braidRels]
      exact Or.inr ⟨0, 1, by decide, rfl⟩)
  have h1 : PresentedGroup.mk (BraidsLinksMCG.braidRels 3)
      (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * FreeGroup.of 0 *
        (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹) = 1 :=
    PresentedGroup.mk_eq_one_iff.mpr hmem
  have h2 : BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1 *
      BraidsLinksMCG.sigma (n := 3) 0 *
      (BraidsLinksMCG.sigma (n := 3) 1 * BraidsLinksMCG.sigma (n := 3) 0 *
        BraidsLinksMCG.sigma (n := 3) 1)⁻¹ = 1 := by
    have hmid : BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1 *
        BraidsLinksMCG.sigma (n := 3) 0 *
        (BraidsLinksMCG.sigma (n := 3) 1 * BraidsLinksMCG.sigma (n := 3) 0 *
          BraidsLinksMCG.sigma (n := 3) 1)⁻¹ =
        (PresentedGroup.mk (BraidsLinksMCG.braidRels 3)
          (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * FreeGroup.of 0 *
            (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹) :
          BraidsLinksMCG.ArtinBraidGroup 3) := by
      simp only [BraidsLinksMCG.sigma, PresentedGroup.of, map_mul, map_inv]
      rfl
    have h1' : (PresentedGroup.mk (BraidsLinksMCG.braidRels 3)
        (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 * FreeGroup.of 0 *
          (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹) :
        BraidsLinksMCG.ArtinBraidGroup 3) = 1 := h1
    exact hmid.trans h1'
  have h : BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1 *
      BraidsLinksMCG.sigma (n := 3) 0 =
      BraidsLinksMCG.sigma (n := 3) 1 * BraidsLinksMCG.sigma (n := 3) 0 *
        BraidsLinksMCG.sigma (n := 3) 1 :=
    mul_inv_eq_one.mp h2
  -- `Δ² = (σ₁σ₂)³`
  have hsq : (BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1 *
        BraidsLinksMCG.sigma (n := 3) 0) ^ 2 =
      (BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1) ^ 3 := by
    rw [pow_two, pow_three]
    nth_rewrite 2 [h]
    simp only [mul_assoc]
  calc (BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1 *
          BraidsLinksMCG.sigma (n := 3) 0) ^ 4
      = ((BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1 *
          BraidsLinksMCG.sigma (n := 3) 0) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = ((BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1) ^ 3) ^ 2 := by
        rw [hsq]
    _ = (BraidsLinksMCG.sigma (n := 3) (0 : Fin 2) * BraidsLinksMCG.sigma (n := 3) 1) ^ 6 := by
        rw [← pow_mul]
