-- Prove2me | solution 1 for FdVersusFdSucc.depth_frege_sound
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T13:50:21.573272+00:00
-- url     : https://prove2.me/submissions/776045c3-dd7e-4c08-8d7c-1a67b4e78320

import Mathlib
import Definitions.Def_FdVersusFdSucc_defs

set_option autoImplicit false

open Filter

namespace FdVersusFdSucc.FrSoundA
open FdVersusFdSucc Formula

theorem eval_and (v : ℕ → Bool) (As : List Formula) :
    (Formula.and As).eval v = true ↔ ∀ A ∈ As, A.eval v = true := by
  simp [Formula.eval]

theorem eval_or (v : ℕ → Bool) (As : List Formula) :
    (Formula.or As).eval v = true ↔ ∃ A ∈ As, A.eval v = true := by
  simp [Formula.eval]

/-- De Morgan duality: the dual of a formula evaluates to the negation. -/
theorem eval_dual (v : ℕ → Bool) (A : Formula) : A.dual.eval v = !(A.eval v) := by
  induction A using Formula.rec (motive_2 := fun As => ∀ A ∈ As, A.dual.eval v = !(A.eval v)) with
  | pos i => simp [Formula.dual, Formula.eval]
  | neg i => simp [Formula.dual, Formula.eval]
  | and As ih =>
      apply Bool.eq_iff_iff.mpr
      rw [Formula.dual.eq_3, eval_or]
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, eval_and]
      constructor
      · rintro ⟨B, hB, hBv⟩ hall
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [ih A hA, hall A hA] at hBv
        simp at hBv
      · intro h
        by_contra hc
        simp only [not_exists, not_and] at hc
        apply h
        intro A hA
        have := hc A.dual (by simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]; exact ⟨A, hA, rfl⟩)
        rw [ih A hA] at this
        cases hAv : A.eval v
        · rw [hAv] at this; exact absurd rfl this
        · rfl
  | or As ih =>
      apply Bool.eq_iff_iff.mpr
      rw [Formula.dual.eq_4, eval_and]
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, eval_or]
      constructor
      · rintro hall ⟨A, hA, hAv⟩
        have := hall A.dual (by simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]; exact ⟨A, hA, rfl⟩)
        rw [ih A hA, hAv] at this
        simp at this
      · intro h B hB
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [ih A hA]
        cases hAv : A.eval v
        · rfl
        · exact absurd ⟨A, hA, hAv⟩ h
  | nil A hA => simp at hA
  | cons B Bs ihB ihBs A hA =>
      rcases List.mem_cons.mp hA with rfl | hA
      · exact ihB
      · exact ihBs A hA

/-- A sequent is valid if under every assignment some member is true. -/
def Valid (Γ : Sequent) : Prop := ∀ v : ℕ → Bool, ∃ B ∈ Γ, B.eval v = true

theorem step_valid (prev : List Sequent) (Γ : Sequent) (hprev : ∀ Δ ∈ prev, Valid Δ)
    (hs : Step prev Γ) : Valid Γ := by
  cases hs with
  | ax Γ i hp hn =>
      intro v
      cases hv : v i
      · exact ⟨neg i, hn, by simp [Formula.eval, hv]⟩
      · exact ⟨pos i, hp, by simp [Formula.eval, hv]⟩
  | andI Γ As h =>
      intro v
      by_cases hc : ∃ B ∈ Γ, B.eval v = true
      · obtain ⟨B, hB, hBv⟩ := hc
        exact ⟨B, List.mem_cons_of_mem _ hB, hBv⟩
      · refine ⟨Formula.and As, List.mem_cons_self, ?_⟩
        simp only [Formula.eval, List.all_eq_true, List.mem_attach, true_implies, Subtype.forall]
        intro A hA
        obtain ⟨B, hB, hBv⟩ := hprev _ (h A hA) v
        rcases List.mem_cons.mp hB with rfl | hB
        · exact hBv
        · exact absurd ⟨B, hB, hBv⟩ hc
  | orI Γ As A hA h =>
      intro v
      obtain ⟨B, hB, hBv⟩ := hprev _ h v
      rcases List.mem_cons.mp hB with rfl | hB
      · refine ⟨Formula.or As, List.mem_cons_self, ?_⟩
        simp only [Formula.eval, List.any_eq_true, List.mem_attach, true_and, Subtype.exists]
        exact ⟨B, hA, hBv⟩
      · exact ⟨B, List.mem_cons_of_mem _ hB, hBv⟩
  | weaken Γ Δ h hsub =>
      intro v
      obtain ⟨B, hB, hBv⟩ := hprev _ h v
      exact ⟨B, hsub hB, hBv⟩
  | cut Γ A h1 h2 =>
      intro v
      obtain ⟨B, hB, hBv⟩ := hprev _ h1 v
      obtain ⟨C, hC, hCv⟩ := hprev _ h2 v
      rcases List.mem_cons.mp hB with rfl | hB
      · rcases List.mem_cons.mp hC with rfl | hC
        · rw [eval_dual, hBv] at hCv
          exact absurd hCv (by decide)
        · exact ⟨C, hC, hCv⟩
      · exact ⟨B, hB, hBv⟩

theorem proof_valid (π : List Sequent) (hπ : ∀ (i : ℕ) (h : i < π.length), Step (π.take i) π[i]) :
    ∀ (i : ℕ) (h : i < π.length), Valid π[i] := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    apply step_valid (π.take i) _ _ (hπ i h)
    intro Δ hΔ
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hΔ
    exact ih j (lt_of_lt_of_le hj (min_le_left _ _)) _

end FdVersusFdSucc.FrSoundA

open FdVersusFdSucc in
theorem solution (d : ℕ) (π : List Sequent) (A : Formula)
    (h : IsDepthProofOf d π A) : A.IsTautology := by
  obtain ⟨⟨hsteps, _⟩, hA⟩ := h
  obtain ⟨i, hi, hiA⟩ := List.mem_iff_getElem.mp hA
  have hv := FrSoundA.proof_valid π hsteps i hi
  rw [hiA] at hv
  intro v
  obtain ⟨B, hB, hBv⟩ := hv v
  rw [List.mem_singleton] at hB
  subst hB
  exact hBv
