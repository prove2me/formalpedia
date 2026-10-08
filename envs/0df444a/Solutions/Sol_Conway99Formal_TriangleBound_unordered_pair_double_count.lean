-- Prove2me | solution 1 for Conway99Formal.TriangleBound.unordered_pair_double_count
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T06:45:38.609986+00:00
-- url     : https://prove2.me/submissions/e395f4ef-0994-47aa-a866-29fa8974465f

import Mathlib

namespace Conway99Formal.TriangleBound
end Conway99Formal.TriangleBound

set_option autoImplicit false

/-! Literal graph counts for the universal triangle and prism claim. -/

namespace Conway99Formal.TriangleBound

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


































end Conway99Formal.TriangleBound

set_option autoImplicit false

/-! Literal graph counts for the universal triangle and prism claim. -/

open Conway99Formal.TriangleBound

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.TriangleBound in
theorem solution {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (R : A → A → Prop) [DecidableRel R]
    (hsym : ∀ a b, R a b → R b a) :
    (∑ a ∈ s, (s.filter fun b => a ≠ b ∧ R a b).card) =
      2 * ((s.powersetCard 2).filter fun p =>
        ∃ a b, a ∈ p ∧ b ∈ p ∧ a ≠ b ∧ R a b).card := by
  classical
  let ordered := (s ×ˢ s).filter fun ab => ab.1 ≠ ab.2 ∧ R ab.1 ab.2
  let pairs := (s.powersetCard 2).filter fun p =>
    ∃ a b, a ∈ p ∧ b ∈ p ∧ a ≠ b ∧ R a b
  have hmap : ∀ ab ∈ ordered, ({ab.1, ab.2} : Finset A) ∈ pairs := by
    intro ab hab
    have hmem := Finset.mem_filter.mp hab
    have hprod := hmem.1
    have hne := hmem.2.1
    have hR := hmem.2.2
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hprod
    simp only [pairs, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, ⟨ab.1, ab.2, by simp, by simp, hne, hR⟩⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · simp [hne]
  have hfiber : ∀ p ∈ pairs,
      ({ab ∈ ordered | ({ab.1, ab.2} : Finset A) = p}).card = 2 := by
    intro p hp
    have hpbase : p ∈ s.powersetCard 2 := (Finset.mem_filter.mp hp).1
    have hpcard : p.card = 2 := (Finset.mem_powersetCard.mp hpbase).2
    obtain ⟨a, b, hab, hpe⟩ := Finset.card_eq_two.mp hpcard
    have hpsub : p ⊆ s := (Finset.mem_powersetCard.mp hpbase).1
    have ha : a ∈ s := hpsub (hpe.symm ▸ (by simp : a ∈ ({a, b} : Finset A)))
    have hb : b ∈ s := hpsub (hpe.symm ▸ (by simp : b ∈ ({a, b} : Finset A)))
    have hR : R a b := by
      obtain ⟨x, y, hx, hy, hxy, hxyR⟩ := (Finset.mem_filter.mp hp).2
      rw [hpe] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact False.elim (hxy rfl)
      · exact hxyR
      · exact hsym _ _ hxyR
      · exact False.elim (hxy rfl)
    have hset : ({ab ∈ ordered | ({ab.1, ab.2} : Finset A) = p}) =
        {(a, b), (b, a)} := by
      ext ab
      constructor
      · intro h
        have hordered : ab ∈ ordered := (Finset.mem_filter.mp h).1
        have heq : ({ab.1, ab.2} : Finset A) = p := (Finset.mem_filter.mp h).2
        have hne : ab.1 ≠ ab.2 := (Finset.mem_filter.mp hordered).2.1
        have hx : ab.1 = a ∨ ab.1 = b := by
          have : ab.1 ∈ ({a, b} : Finset A) := by rw [← hpe, ← heq]; simp
          simpa using this
        have hy : ab.2 = a ∨ ab.2 = b := by
          have : ab.2 ∈ ({a, b} : Finset A) := by rw [← hpe, ← heq]; simp
          simpa using this
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact False.elim (hne (hx.trans hy.symm))
        · exact Finset.mem_insert.mpr (Or.inl (Prod.ext hx hy))
        · exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (Prod.ext hx hy)))
        · exact False.elim (hne (hx.trans hy.symm))
      · intro h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · subst ab
          apply Finset.mem_filter.mpr
          constructor
          · simp [ordered, hab, ha, hb, hR]
          · exact hpe.symm
        · subst ab
          apply Finset.mem_filter.mpr
          constructor
          · simp [ordered, hab.symm, ha, hb, hsym a b hR]
          · exact (Finset.pair_comm b a).trans hpe.symm
    rw [hset]
    simp [hab]
  have hordered :
      (∑ a ∈ s, (s.filter fun b => a ≠ b ∧ R a b).card) = ordered.card := by
    simp only [ordered, Finset.card_eq_sum_ones, Finset.sum_product, Finset.sum_filter]
  rw [hordered]
  calc
    ordered.card = ∑ p ∈ pairs,
        ({ab ∈ ordered | ({ab.1, ab.2} : Finset A) = p}).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun ab hab => hmap ab hab)
    _ = ∑ _p ∈ pairs, 2 := Finset.sum_congr rfl hfiber
    _ = 2 * pairs.card := by simp [mul_comm]
