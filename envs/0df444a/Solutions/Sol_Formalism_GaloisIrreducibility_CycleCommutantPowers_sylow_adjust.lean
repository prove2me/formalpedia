-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.CycleCommutantPowers.sylow_adjust
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:19.291647+00:00
-- url     : https://prove2.me/submissions/715210ed-3064-4e8e-a6ff-ab527ae6263c

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Equiv Equiv.Perm MulAction
open Formalism.GaloisIrreducibility.CycleCommutantPowers
variable {α : Type} [Fintype α] [DecidableEq α]
namespace Formalism.GaloisIrreducibility.CycleCommutantPowers
theorem _root_.solution (G : Subgroup (Perm α)) (g : Perm α) (p : ℕ) (hp : p.Prime)
    (hgG : g ∈ G) (hgc : g.IsCycle) (hgp : g.support.card = p)
    (x : Perm α) (hxG : x ∈ G) (hxΓ : ∀ γ, g γ = γ → g (x⁻¹ γ) = x⁻¹ γ) :
    ∃ f ∈ G, (∀ γ, g γ = γ → f γ = γ) ∧ ∃ e : ℤ, (f * x) * g * (f * x)⁻¹ = g ^ e := by
  classical
  have := Fact.mk hp
  set Γ : Set α := {γ | g γ = γ} with hΓ
  set F : Subgroup (Perm α) := G ⊓ fixingSubgroup (Perm α) Γ with hF
  have memF : ∀ σ, σ ∈ F ↔ σ ∈ G ∧ ∀ γ, g γ = γ → σ γ = γ := by
    intro σ; simp [hF, mem_fixingSubgroup_iff, hΓ, Perm.smul_def]
  have hgF : g ∈ F := (memF g).2 ⟨hgG, fun γ h => h⟩
  have hcF : x * g * x⁻¹ ∈ F := by
    refine (memF _).2 ⟨G.mul_mem (G.mul_mem hxG hgG) (G.inv_mem hxG), fun γ hγ => ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, hxΓ γ hγ, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  have hcardF : Nat.card F ∣ p.factorial := by
    have hle : F ≤ (Perm.ofSubtype : Perm {x // x ∈ g.support} →* Perm α).range := by
      intro σ hσ
      obtain ⟨-, hσΓ⟩ := (memF σ).1 hσ
      have h1 : ∀ t, σ t ∈ g.support ↔ t ∈ g.support := by
        intro t
        simp only [Perm.mem_support, ne_eq, not_iff_not]
        constructor
        · intro h
          have h2 := hσΓ _ h
          have h3 : σ t = t := σ.injective h2
          rw [h3] at h; exact h
        · intro h; rw [hσΓ t h]; exact h
      refine MonoidHom.mem_range.2 ⟨σ.subtypePerm h1, ?_⟩
      apply Perm.ofSubtype_subtypePerm
      intro t ht; rw [Perm.mem_support]; intro h; exact ht (hσΓ t h)
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 := Nat.card_congr (MonoidHom.ofInjective
      (Perm.ofSubtype_injective (p := fun x => x ∈ g.support))).toEquiv
    rw [← h2, Nat.card_perm, Nat.card_eq_finsetCard, hgp] at h1
    exact h1
  have hpF : p ∣ Nat.card F := by
    have := orderOf_dvd_natCard (⟨g, hgF⟩ : F)
    rwa [← orderOf_submonoid, hgc.orderOf, hgp] at this
  have hne : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have hfact : (Nat.card F).factorization p = 1 := by
    apply le_antisymm
    · by_contra h
      push Not at h
      have h2 : p ^ 2 ∣ Nat.card F := (hp.pow_dvd_iff_le_factorization hne).2 h
      have h3 : p ^ 2 ∣ p.factorial := h2.trans hcardF
      rw [← Nat.mul_factorial_pred hp.ne_zero, pow_two] at h3
      have h4 := Nat.dvd_of_mul_dvd_mul_left hp.pos h3
      rw [hp.dvd_factorial] at h4
      have := hp.two_le
      omega
    · exact (hp.pow_dvd_iff_le_factorization hne).1 (by simpa using hpF)
  let g' : F := ⟨g, hgF⟩
  let c' : F := ⟨x * g * x⁻¹, hcF⟩
  have hc1 : Nat.card (Subgroup.zpowers g') = p ^ (Nat.card F).factorization p := by
    rw [hfact, pow_one, Nat.card_zpowers, ← orderOf_submonoid, hgc.orderOf, hgp]
  have hc2 : Nat.card (Subgroup.zpowers c') = p ^ (Nat.card F).factorization p := by
    rw [hfact, pow_one, Nat.card_zpowers, ← orderOf_submonoid]
    show orderOf (x * g * x⁻¹) = p
    rw [(hgc.conj).orderOf, Perm.card_support_conj, hgp]
  let S1 : Sylow p F := Sylow.ofCard _ hc1
  let S2 : Sylow p F := Sylow.ofCard _ hc2
  obtain ⟨f, hf⟩ := MulAction.exists_smul_eq F S2 S1
  have hmem : f * c' * f⁻¹ ∈ Subgroup.zpowers g' := by
    have h1 : c' ∈ (S2 : Subgroup F) := Subgroup.mem_zpowers c'
    have h2 : MulAut.conj f • c' ∈ ((f • S2 : Sylow p F) : Subgroup F) := by
      rw [Sylow.coe_subgroup_smul]; exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hf] at h2
    have h3 : f * c' * f⁻¹ ∈ (S1 : Subgroup F) := by simpa using h2
    exact h3
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hfF := (memF f).1 f.2
  refine ⟨f, hfF.1, hfF.2, e, ?_⟩
  have := congrArg Subtype.val he
  simp only [SubgroupClass.coe_zpow, Subgroup.coe_mul, InvMemClass.coe_inv, g', c'] at this
  rw [this]; group
end Formalism.GaloisIrreducibility.CycleCommutantPowers
