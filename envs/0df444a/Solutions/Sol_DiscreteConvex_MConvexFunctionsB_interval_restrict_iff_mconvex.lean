-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.interval_restrict_iff_mconvex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:29:51.211294+00:00
-- url     : https://prove2.me/submissions/0dd854ca-93cd-4a38-82c0-e0f0741e346a

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

set_option autoImplicit false
set_option linter.unusedSectionVars false

open DiscreteConvex.MConvexFunctionsB

namespace IntRes

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The embedding `ℤ → ℤ ∪ {±∞}`. -/
abbrev ce (n : ℤ) : WithBot (WithTop ℤ) := ((n : WithTop ℤ) : WithBot (WithTop ℤ))

theorem ce_mono {m n : ℤ} (h : m ≤ n) : ce m ≤ ce n :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)

/-- A coordinate lying between two in-box values is in the box. -/
theorem box_between (a b : WithBot (WithTop ℤ)) (s t z : ℤ)
    (hs : a ≤ ce s ∧ ce s ≤ b) (ht : a ≤ ce t ∧ ce t ≤ b)
    (hlo : s ≤ z ∨ t ≤ z) (hhi : z ≤ s ∨ z ≤ t) : a ≤ ce z ∧ ce z ≤ b := by
  constructor
  · rcases hlo with h | h
    · exact hs.1.trans (ce_mono h)
    · exact ht.1.trans (ce_mono h)
  · rcases hhi with h | h
    · exact (ce_mono h).trans hs.2
    · exact (ce_mono h).trans ht.2

end IntRes

open IntRes in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    MExchangeAxiom f ↔
      ∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict f a b)).Nonempty →
        MExchangeAxiom (IntervalRestrict f a b) := by
  constructor
  · intro hf a b _ x hx y hy u hu
    have inbox : ∀ z, z ∈ DomZ (IntervalRestrict f a b) →
        (∀ v, a v ≤ ce (z v) ∧ ce (z v) ≤ b v) ∧ z ∈ DomZ f := by
      intro z hz
      have hz' : IntervalRestrict f a b z ≠ ⊤ := hz
      unfold IntervalRestrict at hz'
      by_cases hc : ∀ v, a v ≤ ce (z v) ∧ ce (z v) ≤ b v
      · rw [if_pos hc] at hz'; exact ⟨hc, hz'⟩
      · rw [if_neg hc] at hz'; exact absurd rfl hz'
    obtain ⟨hxb, hxd⟩ := inbox x hx
    obtain ⟨hyb, hyd⟩ := inbox y hy
    obtain ⟨v, hv, hineq⟩ := hf x hxd y hyd u hu
    simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have huv : u ≠ v := by rintro rfl; omega
    have b1 : ∀ w, a w ≤ ce (x w - CharVec u w + CharVec v w) ∧
        ce (x w - CharVec u w + CharVec v w) ≤ b w := by
      intro w
      refine box_between (a w) (b w) (x w) (y w) _ (hxb w) (hyb w) ?_ ?_ <;>
        simp only [CharVec] <;> by_cases h1 : w = u <;> by_cases h2 : w = v <;>
        simp only [h1, h2, if_true, if_false] <;> subst_vars <;> omega
    have b2 : ∀ w, a w ≤ ce (y w + CharVec u w - CharVec v w) ∧
        ce (y w + CharVec u w - CharVec v w) ≤ b w := by
      intro w
      refine box_between (a w) (b w) (x w) (y w) _ (hxb w) (hyb w) ?_ ?_ <;>
        simp only [CharVec] <;> by_cases h1 : w = u <;> by_cases h2 : w = v <;>
        simp only [h1, h2, if_true, if_false] <;> subst_vars <;> omega
    refine ⟨v, by simp [SuppNeg, hv], ?_⟩
    unfold IntervalRestrict
    rw [if_pos hxb, if_pos hyb, if_pos b1, if_pos b2]
    exact hineq
  · intro h
    rcases (DomZ f).eq_empty_or_nonempty with he | hne
    · intro x hx; rw [he] at hx; exact absurd hx (Set.notMem_empty x)
    · have heq : IntervalRestrict f (fun _ => ⊥) (fun _ => ⊤) = f := by
        funext x
        unfold IntervalRestrict
        rw [if_pos (fun v => ⟨bot_le, le_top⟩)]
      have := h (fun _ => ⊥) (fun _ => ⊤) (by rw [heq]; exact hne)
      rwa [heq] at this

#print axioms solution
