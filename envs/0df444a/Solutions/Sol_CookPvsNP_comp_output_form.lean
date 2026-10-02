-- Prove2me | solution 1 for CookPvsNP.comp_output_form
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:46.009144+00:00
-- url     : https://prove2.me/submissions/e340a2f3-0100-4417-a46e-3898cc098cfe

import Definitions.Def_CookPvsNP_CompConversion

set_option autoImplicit false

open CookPvsNP

private theorem leading {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = List.replicate n none ++ xs.dropWhile Option.isNone := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    cases x with
    | none =>
      obtain ⟨n, h⟩ := ih
      refine ⟨n + 1, ?_⟩
      simpa [List.replicate_succ] using congrArg (List.cons none) h
    | some a => exact ⟨0, by simp⟩

private theorem trailing {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = (xs.reverse.dropWhile Option.isNone).reverse ++ List.replicate n none := by
  obtain ⟨n, h⟩ := leading xs.reverse
  exact ⟨n, by simpa using congrArg List.reverse h⟩

/-- An output equality to an ordinary encoded word determines every cell from the
head rightwards: the word is followed only by explicitly stored trailing blanks. -/
theorem solution {I Γ : Type} (ι : I ↪ Γ) (M : TM Γ) (c : Cfg Γ M.Q) (w : List I)
    (hout : M.output c = w.map (some ∘ ι)) :
    ∃ padding, c = compWordCfg ι c.state c.left w padding := by
  obtain ⟨n, h⟩ := trailing (c.head :: c.right)
  change c.head :: c.right = M.output c ++ List.replicate n none at h
  rw [hout] at h
  rcases c with ⟨q, left, head, right⟩
  cases w with
  | nil =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp [List.replicate_succ] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨n, rfl⟩
  | cons a w =>
    simp at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨n, rfl⟩

#print axioms solution
