-- Prove2me | solution 1 for BurauFaithful.normalClosure_singleton_center
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T11:09:29.8369+00:00
-- url     : https://prove2.me/submissions/52180663-8728-4596-a87a-b16bcd26fd29

/-
`BurauFaithful.normalClosure_singleton_center`: for a **central** element, its normal closure is just
the cyclic subgroup it generates.

This is the last step of the assembly in NOTES_BURAU.md (SESSION 14/15): from the injectivity of
`B_3/⟨Δ⁴⟩ → SL(2,ℤ)` one learns that `β` lies in the normal closure of `Δ⁴ = (σ₀σ₁)⁶`; since
`Δ⁴ = (Δ²)²` is central (Proved: `BurauFaithful.braid_three_fullTwist_central` for `Δ²`, plus the
Garside identity `BurauFaithful.braid_three_garside_pow`), that normal closure is the cyclic
subgroup `⟨Δ⁴⟩`, which is exactly the conclusion `∃ k, β = (σ₀σ₁)^{6k}` of
`BurauFaithful.spec_reduced_kernel_le`.

The proof avoids every closure-inclusion lemma: membership in `closure {g}` is rewritten with
`Subgroup.mem_closure_singleton` as `x = g ^ n`, and membership is then produced by
`Subgroup.zpow_mem` from the centrality of `g` (`Subgroup.mem_center_iff`). Verified names in this
Mathlib: `Subgroup.mem_closure_singleton` (`Algebra/Group/Subgroup/Lattice.lean:468`),
`Subgroup.zpow_mem (H) (hx) (n)`, `Subgroup.mem_center_iff` (`GroupTheory/Subgroup/Center.lean:58`),
`Subgroup.normalClosure_le_normal` (`GroupTheory/Subgroup/Basic.lean:646`).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem solution (G : Type*) [Group G] (g : G) (hg : g ∈ Subgroup.center G) :
    Subgroup.normalClosure ({g} : Set G) = Subgroup.closure ({g} : Set G) := by
  refine le_antisymm ?_ ?_
  · haveI hN : (Subgroup.closure ({g} : Set G)).Normal :=
      ⟨fun x hx y => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hx
        have hpow : g ^ n ∈ Subgroup.center G := Subgroup.zpow_mem (Subgroup.center G) hg n
        have hconj : y * g ^ n * y⁻¹ = g ^ n := by
          calc y * g ^ n * y⁻¹ = g ^ n * y * y⁻¹ := by rw [Subgroup.mem_center_iff.mp hpow y]
            _ = g ^ n := by group
        rw [hconj]
        exact Subgroup.mem_closure_singleton.mpr ⟨n, rfl⟩⟩
    exact Subgroup.normalClosure_le_normal (fun x hx => Subgroup.subset_closure hx)
  · intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hx
    exact Subgroup.zpow_mem (Subgroup.normalClosure ({g} : Set G))
      (Subgroup.subset_normalClosure (by simp)) n
