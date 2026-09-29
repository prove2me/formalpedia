-- Prove2me | solution 1 for FoundationsML.SVM.talagrands_lemma
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T12:16:25.023884+00:00
-- url     : https://prove2.me/submissions/bcc3d6c2-5f46-46a9-818c-7a5466213474

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity

/-! Disproof of f500f416 `FoundationsML.SVM.talagrands_lemma`.

Both sides use `⨆ h ∈ H, F h`, which over `ℝ` is `⨆ h, ⨆ (_ : h ∈ H), F h`. For `h ∉ H` the
inner supremum is over an empty index and `Real` gives it the junk value `sSup ∅ = 0`, so when
`H ≠ univ` each summand is `max (sup_H F) 0`: negative parts are clipped. Take `X = Unit`,
`m = 1`, `H = {0}`, `Φ ≡ 1` (which is `0`-Lipschitz), `l = 0`. The right side is `0`, while the
left side is `(1/2)·(max 1 0 + max (-1) 0) = 1/2`. -/

set_option autoImplicit false

theorem svm_dp_biSup_singleton_ge (c : ℝ) :
    max c 0 ≤ ⨆ h ∈ ({fun _ => 0} : Set (Unit → ℝ)), c := by
  have hbdd : BddAbove (Set.range fun h : Unit → ℝ =>
      ⨆ (_ : h ∈ ({fun _ => 0} : Set (Unit → ℝ))), c) := by
    refine ⟨max c 0, ?_⟩
    rintro _ ⟨h, rfl⟩
    dsimp only
    by_cases hh : h ∈ ({fun _ => 0} : Set (Unit → ℝ))
    · rw [ciSup_pos hh]
      exact le_max_left _ _
    · rw [ciSup_neg hh, Real.sSup_empty]
      exact le_max_right _ _
  have h0 : (fun _ : Unit => (0 : ℝ)) ∈ ({fun _ => 0} : Set (Unit → ℝ)) := rfl
  have h1 : (fun _ : Unit => (1 : ℝ)) ∉ ({fun _ => 0} : Set (Unit → ℝ)) := by
    intro h
    have := congrFun (Set.mem_singleton_iff.mp h) ()
    norm_num at this
  apply max_le
  · refine le_ciSup_of_le hbdd (fun _ => 0) ?_
    rw [ciSup_pos h0]
  · refine le_ciSup_of_le hbdd (fun _ => 1) ?_
    rw [ciSup_neg h1, Real.sSup_empty]

open FoundationsML.SVM in
theorem solution : ¬ (∀ {X : Type} {m : ℕ} (H : Set (X → ℝ)) (S : Fin m → X)
    (Φ : Fin m → ℝ → ℝ) (l : ℝ) (hl : 0 ≤ l)
    (hLip : ∀ i : Fin m, ∀ x y : ℝ, |Φ i x - Φ i y| ≤ l * |x - y|),
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
      ⨆ h ∈ H, (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * Φ i (h (S i))
      ≤ l * EmpiricalRademacherComplexity H S) := by
  intro H
  have key := H (X := Unit) (m := 1) ({fun _ => 0} : Set (Unit → ℝ)) (fun _ => ())
    (fun _ _ => 1) 0 le_rfl (by intro i x y; simp)
  simp only [Nat.cast_one, div_one, one_mul, Fin.sum_univ_one, mul_one, pow_one,
    zero_mul] at key
  have hnn : ∀ σ : Fin 1 → Bool, (0 : ℝ) ≤
      ⨆ h ∈ ({fun _ => 0} : Set (Unit → ℝ)), (if σ 0 then (1 : ℝ) else -1) :=
    fun σ => (le_max_right _ _).trans (svm_dp_biSup_singleton_ge _)
  have htrue : (1 : ℝ) ≤ ⨆ h ∈ ({fun _ => 0} : Set (Unit → ℝ)),
      (if (fun _ => true : Fin 1 → Bool) 0 then (1 : ℝ) else -1) := by
    refine le_trans ?_ (svm_dp_biSup_singleton_ge _)
    simp
  have hsum := Finset.single_le_sum (s := Finset.univ)
    (f := fun σ : Fin 1 → Bool =>
      ⨆ h ∈ ({fun _ => 0} : Set (Unit → ℝ)), (if σ 0 then (1 : ℝ) else -1))
    (fun σ _ => hnn σ) (Finset.mem_univ (fun _ => true))
  linarith
