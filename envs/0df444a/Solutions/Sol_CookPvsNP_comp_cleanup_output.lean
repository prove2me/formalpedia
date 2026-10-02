-- Prove2me | solution 1 for CookPvsNP.comp_cleanup_output
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:46.839433+00:00
-- url     : https://prove2.me/submissions/3f948939-8452-4dcd-856c-6953dde4f861

import Definitions.Def_CookPvsNP_CompCleanup
import Theorems.Thm_CookPvsNP_comp_output_form

set_option autoImplicit false

open CookPvsNP

private theorem clean_blanks {Γ : Type} (b : Bool) (n : ℕ) :
    compCleanTail b (List.replicate n (none : Option Γ)) = List.replicate n none := by
  induction n generalizing b <;> simp [List.replicate_succ, compCleanTail, *]

private theorem clean_word {I Γ : Type} (ι : I ↪ Γ) (w : List I) (n : ℕ) :
    compCleanTail false (w.map (some ∘ ι) ++ List.replicate n none) =
      w.map (some ∘ ι) ++ List.replicate n none := by
  induction w <;> simp [compCleanTail, clean_blanks, *]

private theorem trim_blanks {Γ : Type} (xs : List (Option Γ)) (n : ℕ) :
    ((xs ++ List.replicate n none).reverse.dropWhile Option.isNone).reverse =
      (xs.reverse.dropWhile Option.isNone).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    simpa using ih

private theorem trim_word {I Γ : Type} (ι : I ↪ Γ) (w : List I) :
    ((w.map (some ∘ ι)).reverse.dropWhile Option.isNone).reverse = w.map (some ∘ ι) := by
  have h (xs : List I) : (xs.map (some ∘ ι)).dropWhile Option.isNone = xs.map (some ∘ ι) := by
    cases xs <;> simp
  rw [← List.map_reverse, h, ← List.map_reverse, List.reverse_reverse]

/-- Cleanup preserves the ordinary word output, erasing the first track and markers. -/
theorem solution {I S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (ι : I ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : CompSecondFrame A B M₂.Q) (w : List I)
    (hout : M₂.output c.source = w.map (some ∘ ι)) :
    (compTM j₁ j₂ M₁ M₂).output (compCleanCfg c) =
      w.map (some ∘ compOutputEmbedding ι) := by
  obtain ⟨n, h⟩ := comp_output_form ι M₂ c.source w hout
  have hh := congrArg Cfg.head h
  have hr := congrArg Cfg.right h
  simp only [CompSecondFrame.source, compWordCfg] at hh hr
  have hn : CompCell.secondSymbol (Γ₁ := A) (none : Option B) = none := rfl
  have hs (x : I) : CompCell.secondSymbol (Γ₁ := A) (some (ι x)) =
      some (compOutputEmbedding ι x) := by
    simp [CompCell.secondSymbol, CompCell.plain, CompCell.pack, compOutputEmbedding]
    rfl
  cases w with
  | nil =>
    simp only [List.map_nil, List.headD_nil, List.tail_nil, List.nil_append] at hh hr
    simp [TM.output, compCleanCfg, hh, hr, clean_blanks, hn, List.replicate_succ,
      ← List.replicate_add]
  | cons x xs =>
    simp only [List.map_cons, List.headD_cons, List.tail_cons] at hh hr
    simp only [TM.output, compCleanCfg, hh, hr]
    rw [show ((some ∘ ι) x).isNone = false from rfl, clean_word ι xs n]
    simp only [List.map_append, List.map_replicate, hn, List.map_map, Function.comp_def, hs]
    rw [List.append_assoc, ← List.replicate_add, ← List.cons_append]
    rw [trim_blanks]
    exact trim_word (compOutputEmbedding ι) (x :: xs)

#print axioms solution
