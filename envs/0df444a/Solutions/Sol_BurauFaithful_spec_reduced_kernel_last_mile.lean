-- Prove2me | solution 1 for BurauFaithful.spec_reduced_kernel_last_mile
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T11:43:44.91725+00:00
-- url     : https://prove2.me/submissions/4984a98e-2f43-441f-b148-507b04e1c2eb

/-
`BurauFaithful.spec_reduced_kernel_last_mile`: the final algebraic step of
`BurauFaithful.spec_reduced_kernel_le`.

That node asks: if `β ∈ B₃` is killed by the specialization at `t = -1`, then `β = (σ₀σ₁)^{6k}` for
some integer `k`. Everything needed for the *last mile* is:

* the Proved platform node `BurauFaithful.braid_three_fullTwist_central` — `Δ² = (σ₀σ₁)³` is central
  in `B₃`, hence so is `Δ⁴ = (σ₀σ₁)⁶ = (Δ²)²` (the centre is a subgroup);
* the accepted node `BurauFaithful.normalClosure_singleton_center` — the normal closure of a
  **central** element `g` is just its cyclic subgroup `⟨g⟩`.

Hence, once the injectivity side of the story has produced `β ∈ normalClosure {(σ₀σ₁)⁶}`, this lemma
rewrites that membership as an explicit power:
`β ∈ ⟨(σ₀σ₁)⁶⟩`, i.e. `β = ((σ₀σ₁)⁶)^k = (σ₀σ₁)^{6k}` for some `k ∈ ℤ`.

NOTE (platform rule): this file imports only **Proved/Accepted** nodes. Importing an Open node into a
problem statement is rejected by the platform ("Imported platform theorems must be Proved at
submission time"); that is also why the centrality of `(σ₀σ₁)⁶` is derived here from the Proved `Δ²`
node rather than imported from `BurauFaithful.braid_three_garside_sixth_central` (itself still Open).
-/
import Theorems.Thm_BurauFaithful_normalClosure_singleton_center
import Theorems.Thm_BurauFaithful_braid_three_fullTwist_central

set_option autoImplicit false

theorem solution (β : BraidsLinksMCG.ArtinBraidGroup 3)
    (hβ : β ∈ Subgroup.normalClosure
      ({(BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩) ^ 6} :
          Set (BraidsLinksMCG.ArtinBraidGroup 3))) :
    ∃ k : ℤ, β = (BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩ *
      BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩) ^ (6 * k) := by
  set g : BraidsLinksMCG.ArtinBraidGroup 3 := BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩ *
    BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩ with hg
  have h3 : g ^ 3 ∈ Subgroup.center (BraidsLinksMCG.ArtinBraidGroup 3) := by
    simpa only [← hg] using BurauFaithful.braid_three_fullTwist_central
  have hcent : g ^ 6 ∈ Subgroup.center (BraidsLinksMCG.ArtinBraidGroup 3) := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
    exact Subgroup.pow_mem (Subgroup.center (BraidsLinksMCG.ArtinBraidGroup 3)) h3 2
  have hnc : β ∈ Subgroup.closure ({g ^ 6} : Set (BraidsLinksMCG.ArtinBraidGroup 3)) := by
    rw [← BurauFaithful.normalClosure_singleton_center (BraidsLinksMCG.ArtinBraidGroup 3)
      (g ^ 6) hcent]
    simpa only [← hg] using hβ
  obtain ⟨n, hn⟩ := Subgroup.mem_closure_singleton.mp hnc
  exact ⟨n, by rw [zpow_mul]; exact hn.symm⟩
