-- Prove2me | solution 1 for CannonFloydParry.mk_sigmaGen_zero_eq_mk_sigmaGen_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T11:34:04.882996+00:00
-- url     : https://prove2.me/submissions/43d9d04a-d5b2-4ac9-b9ee-f6d26b1a5902

import Definitions.Def_CannonFloydParry_V
import Mathlib

/-! In every proper quotient of `Σ`, `s₀` and `s₁` have the same image (CFP p. 247). -/

namespace CannonFloydParry.S6

open Equiv Equiv.Perm

instance (K : ℕ) : Fintype {x : ℕ // x < K} := Fintype.ofEquiv _ Fin.equivSubtype

/-- The permutations of `{0, …, K-1}`, extended by the identity, as elements of `Σ`. -/
def iotaK (K : ℕ) : Perm {x : ℕ // x < K} →* SigmaPerm :=
  (ofSubtype : Perm {x : ℕ // x < K} →* Perm ℕ).codRestrict SigmaPerm fun τ =>
    (Set.finite_lt_nat K).subset fun x hx => by
      by_contra h
      exact hx (ofSubtype_apply_of_not_mem τ h)

lemma iotaK_coe (K : ℕ) (τ : Perm {x : ℕ // x < K}) : (iotaK K τ : Perm ℕ) = ofSubtype τ := rfl

lemma sigmaGen_inv (i : ℕ) : (sigmaGen i)⁻¹ = sigmaGen i :=
  Subtype.ext (swap_inv _ _)

theorem mk_sigmaGen_zero_eq_mk_sigmaGen_one' (N : Subgroup SigmaPerm) [N.Normal] (hN : N ≠ ⊥) :
    (QuotientGroup.mk (sigmaGen 0) : SigmaPerm ⧸ N) = QuotientGroup.mk (sigmaGen 1) := by
  obtain ⟨⟨σ, hσN⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN
  obtain ⟨b, hb⟩ := σ.2.bddAbove
  set K := max (b + 1) 5 with hK
  have hmove : ∀ x, (σ : Perm ℕ) x ≠ x → x < K := fun x hx =>
    lt_of_le_of_lt (hb hx) (by omega)
  have h₁ : ∀ x, (σ : Perm ℕ) x < K ↔ x < K := by
    intro x
    by_cases hx : (σ : Perm ℕ) x = x
    · rw [hx]
    · refine ⟨fun _ => hmove x hx, fun _ => hmove _ fun h => hx ?_⟩
      exact (σ : Perm ℕ).injective h
  set τ : Perm {x : ℕ // x < K} := (σ : Perm ℕ).subtypePerm h₁
  have hτ : iotaK K τ = σ := Subtype.ext (ofSubtype_subtypePerm h₁ hmove)
  set M := N.comap (iotaK K)
  haveI : M.Normal := Subgroup.Normal.comap inferInstance _
  have hτM : τ ∈ M := by show iotaK K τ ∈ N; rw [hτ]; exact hσN
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hσ1
    apply Subtype.ext
    show σ = 1
    rw [← hτ, h, map_one]
  haveI : Nontrivial M := ⟨⟨⟨τ, hτM⟩, 1, fun h => hτ1 (congrArg Subtype.val h)⟩⟩
  have hcard : 5 ≤ Nat.card {x : ℕ // x < K} := by
    rw [← Nat.card_congr (Fin.equivSubtype (n := K)), Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have hA := alternatingGroup_le_of_normal hcard (N := M) inferInstance
  set a : {x : ℕ // x < K} := ⟨0, by omega⟩
  set b1 : {x : ℕ // x < K} := ⟨1, by omega⟩
  set c : {x : ℕ // x < K} := ⟨2, by omega⟩
  have hg : swap a b1 * swap b1 c ∈ alternatingGroup {x : ℕ // x < K} := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap, sign_swap]
    · rfl
    · simp [b1, c, Subtype.ext_iff]
    · simp [a, b1, Subtype.ext_iff]
  have hgN : iotaK K (swap a b1 * swap b1 c) ∈ N := hA hg
  have e : iotaK K (swap a b1 * swap b1 c) = sigmaGen 0 * sigmaGen 1 := by
    rw [map_mul]
    congr 1 <;> exact Subtype.ext (by rw [iotaK_coe, ofSubtype_swap_eq]; rfl)
  rw [e] at hgN
  rw [QuotientGroup.eq, sigmaGen_inv]
  exact hgN

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution (N : Subgroup SigmaPerm) [N.Normal] (hN : N ≠ ⊥) :
    (QuotientGroup.mk (sigmaGen 0) : SigmaPerm ⧸ N) = QuotientGroup.mk (sigmaGen 1) := by
  exact S6.mk_sigmaGen_zero_eq_mk_sigmaGen_one' N hN
