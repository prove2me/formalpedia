-- Prove2me | solution 1 for FiniteMaximizer__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:16:28.433127+00:00
-- url     : https://prove2.me/submissions/da65905c-8465-4df9-a910-e7b8ece443b6

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) (P : α → Prop) (w : α → Nat)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hmono : ∀ a b, r a b → w a ≤ w b)
    (hstrict : ∀ a b, r a b → ¬ r b a → w a < w b)
    (a : α) (ha : P a) :
    ∃ b, r a b ∧ P b ∧
      (∀ c, r b c → P c → r c b) ∧ w a ≤ w b := by
  classical
  let s : Finset α := Finset.univ.filter (fun x => r a x ∧ P x)
  have hne : s.Nonempty := by
    refine ⟨a, ?_⟩
    simp [s, hrefl a, ha]
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image s w hne
  have hab : r a b := (Finset.mem_filter.mp hb).2.1
  have hPb : P b := (Finset.mem_filter.mp hb).2.2
  refine ⟨b, hab, hPb, ?_, hmono a b hab⟩
  intro c hbc hPc
  have hc : c ∈ s := by
    simp [s, htrans a b c hab hbc, hPc]
  by_contra hcb
  exact (not_lt_of_ge (hmax c hc)) (hstrict b c hbc hcb)