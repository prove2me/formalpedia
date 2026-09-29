-- Prove2me | solution 1 for Chou.hall_finite_subgroups_of_index
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T23:13:44.184985+00:00
-- url     : https://prove2.me/submissions/d282e2eb-c153-48cd-badb-021c80a62ef6

import Mathlib

/-!
# M. Hall's theorem: a finitely generated group has finitely many subgroups of each finite index

A subgroup `H` of index `n ≠ 0` gives a transitive action of `G` on `G ⧸ H`, a set of `n`
elements; transporting it along a bijection `e : G ⧸ H ≃ Fin n` gives a homomorphism
`G →* Equiv.Perm (Fin n)` together with the base point `e (1 : G ⧸ H)`, and `H` is recovered
from that pair as the stabiliser of the base point.  Since `G` is finitely generated and
`Equiv.Perm (Fin n)` is finite, there are only finitely many such homomorphisms, so only
finitely many such subgroups.
-/

/-- Homomorphisms from a finitely generated group to a finite monoid are determined by their
values on a finite generating set, hence form a finite type. -/
private lemma hallFiniteMonoidHom (G : Type*) [Group G] [hfg : Group.FG G]
    (M : Type*) [Monoid M] [Finite M] : Finite (G →* M) := by
  classical
  obtain ⟨S, hS⟩ := hfg.out
  have hinj : Function.Injective
      (fun f : G →* M => fun s : {x // x ∈ S} => f (s : G)) := by
    intro f₁ f₂ hf
    have hf' : ∀ s : {x // x ∈ S}, f₁ (s : G) = f₂ (s : G) := fun s => congrFun hf s
    refine MonoidHom.eq_of_eqOn_dense hS ?_
    intro x hx
    exact hf' ⟨x, Finset.mem_coe.mp hx⟩
  exact Finite.of_injective _ hinj

/-- The permutation representation of `G` on the coset space `G ⧸ H`, transported along a
bijection `e : G ⧸ H ≃ Fin n`. -/
private def hallPermRep {G : Type*} [Group G] (H : Subgroup G) {n : ℕ}
    (e : G ⧸ H ≃ Fin n) : G →* Equiv.Perm (Fin n) where
  toFun g :=
    { toFun := fun i => e (g • e.symm i)
      invFun := fun i => e (g⁻¹ • e.symm i)
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp [mul_smul]

@[simp]
private lemma hallPermRep_apply {G : Type*} [Group G] (H : Subgroup G) {n : ℕ}
    (e : G ⧸ H ≃ Fin n) (g : G) (i : Fin n) :
    hallPermRep H e g i = e (g • e.symm i) := rfl

/-- `H` is exactly the stabiliser of the base point of its own permutation representation. -/
private lemma hallMem_iff {G : Type*} [Group G] (H : Subgroup G) {n : ℕ}
    (e : G ⧸ H ≃ Fin n) (g : G) :
    g ∈ H ↔ hallPermRep H e g (e ((1 : G) : G ⧸ H)) = e ((1 : G) : G ⧸ H) := by
  rw [hallPermRep_apply, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]
  first
  | (rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]; done)
  | (rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one,
      Subgroup.inv_mem_iff]; done)
  | (simp [MulAction.Quotient.smul_coe, QuotientGroup.eq]; done)
  | simp [MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]

theorem solution {G : Type*} [Group G] [Group.FG G] (n : ℕ) (hn : n ≠ 0) :
    Finite {H : Subgroup G // H.index = n} := by
  classical
  haveI : Finite (G →* Equiv.Perm (Fin n)) := hallFiniteMonoidHom G (Equiv.Perm (Fin n))
  have hq : ∀ H : {H : Subgroup G // H.index = n}, Finite (G ⧸ (H : Subgroup G)) := by
    intro H
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card, H.2]
    exact hn
  have hcard : ∀ H : {H : Subgroup G // H.index = n},
      Nat.card (G ⧸ (H : Subgroup G)) = n := by
    intro H
    rw [← Subgroup.index_eq_card]
    exact H.2
  obtain ⟨e, -⟩ :
      ∃ _e : ∀ H : {H : Subgroup G // H.index = n}, (G ⧸ (H : Subgroup G)) ≃ Fin n, True :=
    ⟨fun H => @Finite.equivFinOfCardEq _ (hq H) n (hcard H), trivial⟩
  refine Finite.of_injective
    (fun H : {H : Subgroup G // H.index = n} =>
      ((hallPermRep (H : Subgroup G) (e H), e H ((1 : G) : G ⧸ (H : Subgroup G))) :
        (G →* Equiv.Perm (Fin n)) × Fin n)) ?_
  intro H K hHK
  have h1 : hallPermRep (H : Subgroup G) (e H) = hallPermRep (K : Subgroup G) (e K) :=
    congrArg Prod.fst hHK
  have h2 : e H ((1 : G) : G ⧸ (H : Subgroup G)) = e K ((1 : G) : G ⧸ (K : Subgroup G)) :=
    congrArg Prod.snd hHK
  refine Subtype.ext (SetLike.ext fun g => ?_)
  rw [hallMem_iff (H : Subgroup G) (e H) g, hallMem_iff (K : Subgroup G) (e K) g, h1, h2]