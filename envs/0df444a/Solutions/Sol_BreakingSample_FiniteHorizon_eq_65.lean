-- Prove2me | solution 1 for BreakingSample.FiniteHorizon.eq_65
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T04:29:06.655775+00:00
-- url     : https://prove2.me/submissions/7fdfe4f3-c90a-4b59-b297-5689eec0da0d

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model

namespace Aux_BSFHeq65
open BreakingSample.FiniteHorizon FoundationsML.ReinforcementLearning

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {H : ℕ}

lemma value_zero (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (π : Fin H → S → A)
    (h : ℕ) (hh : H ≤ h) (s : S) : value P r π h s = 0 := by
  unfold value
  rw [propagate, dif_neg (by omega)]

lemma value_succ (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (π : Fin H → S → A)
    (h : ℕ) (hh : h < H) (s : S) : value P r π h s =
      r ⟨h, hh⟩ s (π ⟨h, hh⟩ s) + ∑ s', P ⟨h, hh⟩ s (π ⟨h, hh⟩ s) s' * value P r π (h + 1) s' := by
  unfold value
  rw [propagate, dif_pos hh]

lemma opt_zero (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (h : ℕ) (hh : H ≤ h) (s : S) :
    optValue P r h s = 0 := by
  unfold optValue
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun π _ => (value_zero P r π h hh s).le)
  · obtain ⟨π⟩ : Nonempty (Fin H → S → A) := inferInstance
    calc (0 : ℝ) = value P r π h s := (value_zero P r π h hh s).symm
      _ ≤ _ := Finset.le_sup' (fun π => value P r π h s) (Finset.mem_univ π)

lemma dp_opt (Phat : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ)
    (hPhat : ∀ h, IsTransitionKernel (Phat h))
    (sel : Fin H → S → (A → ℝ) → A) (hsel : IsArgmaxRule sel) :
    ∀ n : ℕ, ∀ h : ℕ, H ≤ h + n → ∀ s,
      value Phat r (dpPolicy Phat r sel) h s = optValue Phat r h s := by
  intro n
  induction n with
  | zero =>
    intro h hh s
    rw [value_zero _ _ _ h (by omega), opt_zero _ _ h (by omega)]
  | succ n ih =>
    intro h hh s
    by_cases hH : H ≤ h
    · rw [value_zero _ _ _ h hH, opt_zero _ _ h hH]
    push Not at hH
    have ih' : ∀ s', value Phat r (dpPolicy Phat r sel) (h + 1) s' =
        optValue Phat r (h + 1) s' := ih (h + 1) (by omega)
    have hdp : value Phat r (dpPolicy Phat r sel) h s =
        optQ Phat r ⟨h, hH⟩ s (dpPolicy Phat r sel ⟨h, hH⟩ s) := by
      rw [value_succ _ _ _ h hH]
      unfold optQ
      simp only [ih']
    apply le_antisymm
    · exact Finset.le_sup' (fun π => value Phat r π h s) (Finset.mem_univ _)
    · rw [hdp]
      unfold optValue
      apply Finset.sup'_le
      intro π _
      rw [value_succ _ _ _ h hH]
      calc r ⟨h, hH⟩ s (π ⟨h, hH⟩ s) +
            ∑ s', Phat ⟨h, hH⟩ s (π ⟨h, hH⟩ s) s' * value Phat r π (h + 1) s'
          ≤ optQ Phat r ⟨h, hH⟩ s (π ⟨h, hH⟩ s) := by
            unfold optQ
            apply add_le_add le_rfl
            apply Finset.sum_le_sum
            intro s' _
            apply mul_le_mul_of_nonneg_left _ ((hPhat ⟨h, hH⟩ s (π ⟨h, hH⟩ s)).1 s')
            exact Finset.le_sup' (fun π => value Phat r π (h + 1) s') (Finset.mem_univ π)
        _ ≤ optQ Phat r ⟨h, hH⟩ s (dpPolicy Phat r sel ⟨h, hH⟩ s) :=
            hsel ⟨h, hH⟩ s (optQ Phat r ⟨h, hH⟩ s) (π ⟨h, hH⟩ s)

end Aux_BSFHeq65

open BreakingSample.FiniteHorizon FoundationsML.ReinforcementLearning Aux_BSFHeq65 in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {H : ℕ}
    (P Phat : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (hM : IsFHMDP P r)
    (hPhat : ∀ h, IsTransitionKernel (Phat h))
    (sel : Fin H → S → (A → ℝ) → A) (hsel : IsArgmaxRule sel)
    (πstar : Fin H → S → A) (hstar : IsOptimal P r πstar) :
    ∀ (h : Fin H) (s : S),
      optValue P r h.val s - value P r (dpPolicy Phat r sel) h.val s =
          (value Phat r (dpPolicy Phat r sel) h.val s - value P r (dpPolicy Phat r sel) h.val s) +
            (value Phat r πstar h.val s - value Phat r (dpPolicy Phat r sel) h.val s) +
            (optValue P r h.val s - value Phat r πstar h.val s) ∧
      optValue P r h.val s - value P r (dpPolicy Phat r sel) h.val s ≤
          (value Phat r (dpPolicy Phat r sel) h.val s - value P r (dpPolicy Phat r sel) h.val s) +
            (value P r πstar h.val s - value Phat r πstar h.val s) := by
  intro h s
  refine ⟨by ring, ?_⟩
  have h1 : value Phat r πstar h.val s ≤ value Phat r (dpPolicy Phat r sel) h.val s := by
    rw [dp_opt Phat r hPhat sel hsel H h.val (by omega) s]
    exact Finset.le_sup' (fun π => value Phat r π h.val s) (Finset.mem_univ πstar)
  have h2 := hstar h s
  linarith
