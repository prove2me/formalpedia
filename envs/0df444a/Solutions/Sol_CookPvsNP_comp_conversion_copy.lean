-- Prove2me | solution 1 for CookPvsNP.comp_conversion_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:43.024604+00:00
-- url     : https://prove2.me/submissions/d6719f14-dbd7-4122-b271-c42cdf4c3184

import Definitions.Def_CookPvsNP_CompConversion
import Theorems.Thm_CookPvsNP_comp_cell_laws

set_option autoImplicit false
open CookPvsNP

/-- Conversion copies each encoded nonblank symbol to the second track in one step. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B) (xs : List S)
    (left right : List (Option (CompCell A B))) :
    (compTM j₁ j₂ M₁ M₂).run xs.length
      ⟨.convCopy false, left,
        (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ right).headD none,
        (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ right).tail⟩ =
      ⟨.convCopy false,
        (xs.map (fun x => CompCell.plain (some (j₁ x)) (some (j₂ x)))).reverse ++ left,
        right.headD none, right.tail⟩ := by
  induction xs generalizing left with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs (L R : List (Option (CompCell A B))) :
        (compTM j₁ j₂ M₁ M₂).step ⟨.convCopy false, L, CompCell.firstSymbol (some (j₁ x)), R⟩ =
          ⟨.convCopy false, CompCell.plain (some (j₁ x)) (some (j₂ x)) :: L,
            R.headD none, R.tail⟩ := by
      simp [TM.step, TM.IsHalting, compTM, CompCell.firstSymbol, CompCell.plain,
        (comp_cell_laws j₁ j₂).1, (comp_cell_laws j₁ j₂).2.2]
    rw [hs]
    simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih (CompCell.plain (some (j₁ x)) (some (j₂ x)) :: left)

#print axioms solution
