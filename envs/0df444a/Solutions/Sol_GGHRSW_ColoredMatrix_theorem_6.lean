-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T00:26:55.664767+00:00
-- url     : https://prove2.me/submissions/fece13a8-4470-4a2e-a661-9e8d46f5ce04

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model
import Theorems.Thm_GGHRSW_ColoredMatrix_theorem_6_simulation

open GGHRSW.ColoredMatrix

/-- If two random variables `v` and `s` agree outside a bad set, the event `o x (v x)` is contained
in the event `o x (s x)` together with the bad set. -/
lemma card_filter_le_add_card_ne {U V : Type} [Fintype U] [DecidableEq V]
    (o : U → V → Bool) (v s : U → V) :
    (Finset.univ.filter fun x => o x (v x) = true).card ≤
      (Finset.univ.filter fun x => o x (s x) = true).card +
        (Finset.univ.filter fun x => v x ≠ s x).card := by
  classical
  calc (Finset.univ.filter fun x => o x (v x) = true).card
      ≤ ((Finset.univ.filter fun x => o x (s x) = true) ∪
          (Finset.univ.filter fun x => v x ≠ s x)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
        by_cases h : v x = s x
        · left
          rw [← h]
          exact hx
        · right
          exact h
    _ ≤ _ := Finset.card_union_le _ _

/-- With `n = 0` steps both programs contribute no step records, so the initial databases (and hence
the views and acceptance probabilities) for any two assignments coincide. -/
lemma acceptProb_eq_of_n_eq_zero (p : ℕ) [Fact p.Prime] (bp : BP) (hn : bp.n = 0)
    (J : Finset (Fin bp.ℓ)) (σ σ' : Fin bp.ℓ → Bool) (A : Adversary p) :
    acceptProb p bp J σ A = acceptProb p bp J σ' A := by
  have : IsEmpty (Fin bp.n) := by rw [hn]; infer_instance
  have hnil : ∀ l : List (Fin bp.n), l = [] := by
    intro l
    cases l with
    | nil => rfl
    | cons a _ => exact isEmptyElim a
  have hrecs : ∀ (τ : Fin bp.ℓ → Bool) (ω : Sample p bp) (b : Bool),
      programRecs bp J τ ω b = [] := by
    intro τ ω b
    unfold programRecs
    rw [hnil ((List.finRange bp.n).filter fun i => bp.inp i ∈ J),
      hnil ((List.finRange bp.n).filter fun i => bp.inp i ∉ J)]
    rfl
  have hview : ∀ (c : Fin A.K) (ω : Sample p bp), view bp J σ A c ω = view bp J σ' A c ω := by
    intro c ω
    unfold view initDB
    simp only [hrecs]
  unfold acceptProb
  simp only [hview]

theorem solution : ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime] (bp : BP) (J : Finset (Fin bp.ℓ))
    (σ σ' : Fin bp.ℓ → Bool), FunctionallyEquivalent bp J σ σ' →
    ∀ A : Adversary p,
      |acceptProb p bp J σ A - acceptProb p bp J σ' A| ≤
        C * bp.n * ((dbSize bp J + A.q : ℕ) : ℝ) ^ 2 / p := by
  obtain ⟨C, hC⟩ := theorem_6_simulation
  refine ⟨2 * C, ?_⟩
  intro p _ bp J σ σ' hFE A
  rcases Nat.eq_zero_or_pos bp.n with hn | hn
  · -- A program with no steps: the initial database does not depend on the assignment.
    rw [acceptProb_eq_of_n_eq_zero p bp hn J σ σ' A, sub_self, abs_zero, hn]
    simp
  obtain ⟨Sim, hSim⟩ := hC p bp hn J A
  -- Functional equivalence: the simulator receives the same restricted function in both worlds.
  have hF : (fun χ => bp.eval (fix J σ χ)) = (fun χ => bp.eval (fix J σ' χ)) := funext hFE
  have h1 := hSim σ
  have h2 := hSim σ'
  rw [← hF] at h2
  set ε := C * bp.n * ((dbSize bp J + A.q : ℕ) : ℝ) ^ 2 / p with hε
  set S : Fin A.K × Sample p bp → List (Option ℕ) :=
    fun x => Sim (fun χ => bp.eval (fix J σ χ)) x.1 with hS
  set o : Fin A.K × Sample p bp → List (Option ℕ) → Bool := fun x w => A.out x.1 w with ho
  set v : Fin A.K × Sample p bp → List (Option ℕ) := fun x => view bp J σ A x.1 x.2 with hv
  set v' : Fin A.K × Sample p bp → List (Option ℕ) := fun x => view bp J σ' A x.1 x.2 with hv'
  -- The four counting inequalities (accept events versus the simulated accept event).
  have e1 := card_filter_le_add_card_ne o v S
  have e2 := card_filter_le_add_card_ne o S v
  have e3 := card_filter_le_add_card_ne o v' S
  have e4 := card_filter_le_add_card_ne o S v'
  have sym : ∀ w : Fin A.K × Sample p bp → List (Option ℕ),
      (Finset.univ.filter fun x => S x ≠ w x) = (Finset.univ.filter fun x => w x ≠ S x) := by
    intro w
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_comm
  rw [sym] at e2 e4
  set N : ℝ := (Fintype.card (Fin A.K × Sample p bp) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set a : ℝ := ((Finset.univ.filter fun x => o x (v x) = true).card : ℝ) with ha
  set a' : ℝ := ((Finset.univ.filter fun x => o x (v' x) = true).card : ℝ) with ha'
  set g : ℝ := ((Finset.univ.filter fun x => o x (S x) = true).card : ℝ) with hg
  set b : ℝ := ((Finset.univ.filter fun x => v x ≠ S x).card : ℝ) with hb
  set b' : ℝ := ((Finset.univ.filter fun x => v' x ≠ S x).card : ℝ) with hb'
  have r1 : a ≤ g + b := by rw [ha, hg, hb]; exact_mod_cast e1
  have r2 : g ≤ a + b := by rw [ha, hg, hb]; exact_mod_cast e2
  have r3 : a' ≤ g + b' := by rw [ha', hg, hb']; exact_mod_cast e3
  have r4 : g ≤ a' + b' := by rw [ha', hg, hb']; exact_mod_cast e4
  have hP : acceptProb p bp J σ A = a / N := rfl
  have hP' : acceptProb p bp J σ' A = a' / N := rfl
  have hb1 : b / N ≤ ε := h1
  have hb2 : b' / N ≤ ε := h2
  have hdiff : |a - a'| ≤ b + b' := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  rw [hP, hP', ← sub_div, abs_div, abs_of_nonneg hN0]
  calc |a - a'| / N ≤ (b + b') / N := by gcongr
    _ = b / N + b' / N := add_div _ _ _
    _ ≤ ε + ε := add_le_add hb1 hb2
    _ = 2 * C * bp.n * ((dbSize bp J + A.q : ℕ) : ℝ) ^ 2 / p := by rw [hε]; ring
