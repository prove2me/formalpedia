-- Prove2me | solution 1 for BurauFaithful.braid_three_garside_sixth_central
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T11:29:34.628775+00:00
-- url     : https://prove2.me/submissions/3601ebf7-aeb7-4c2e-acda-04b36da29240

/-
`BurauFaithful.braid_three_garside_sixth_central`: the kernel generator `(σ₀σ₁)⁶ = Δ⁴` is central
in `B₃`.

This is the B₃-side input of the assembly in NOTES_BURAU.md (SESSION 14/15): the conclusion of
`BurauFaithful.spec_reduced_kernel_le` is `∃ k, β = (σ₀σ₁)^{6k}`, obtained by applying the general
lemma `BurauFaithful.normalClosure_singleton_center` (normal closure of a *central* element = its
cyclic subgroup) to `g = (σ₀σ₁)⁶`.

Immediate from the Proved platform node `BurauFaithful.braid_three_fullTwist_central`
(`(σ₀σ₁)³` is central): the centre is a subgroup, hence closed under squares, and
`((σ₀σ₁)³)² = (σ₀σ₁)⁶`.
-/
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Theorems.Thm_BurauFaithful_braid_three_fullTwist_central

set_option autoImplicit false

theorem solution :
    (BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩) ^ 6 ∈
      Subgroup.center (BraidsLinksMCG.ArtinBraidGroup 3) := by
  have h3 := BurauFaithful.braid_three_fullTwist_central
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
  exact Subgroup.pow_mem (Subgroup.center (BraidsLinksMCG.ArtinBraidGroup 3)) h3 2
