-- Prove2me | solution 1 for CookPvsNP.comp_conversion_seek
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:43.844329+00:00
-- url     : https://prove2.me/submissions/fa9e9566-7b57-4fa5-82af-010e4d8af495

import Definitions.Def_CookPvsNP_CompConversion

set_option autoImplicit false
open CookPvsNP

/-- After placing the new right boundary, conversion erases the old one beyond the padding. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (n : ℕ) (left : List (Option (CompCell A B))) :
    (compTM j₁ j₂ M₁ M₂).run (n + 1)
      ⟨.convSeekOldRight, left,
        (List.replicate n none ++ [CompCell.rightMarker]).headD none,
        (List.replicate n none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.convReturn, (List.replicate n none ++ left).tail,
        (List.replicate n none ++ left).headD none, [none]⟩ := by
  induction n generalizing left with
  | zero =>
    cases left <;> simp [TM.run, TM.step, TM.IsHalting, compTM, CompCell.rightMarker,
      CompCell.pack, CompCell.unpack, CompCell.blank]
  | succ n ih =>
    simp only [TM.run, Function.iterate_succ_apply, List.replicate_succ, List.cons_append,
      List.headD_cons, List.tail_cons]
    have hs (L R : List (Option (CompCell A B))) :
        (compTM j₁ j₂ M₁ M₂).step ⟨.convSeekOldRight, L, none, R⟩ =
          ⟨.convSeekOldRight, none :: L, R.headD none, R.tail⟩ := by
      simp [TM.step, TM.IsHalting, compTM, CompCell.unpack, CompCell.blank, CompCell.pack]
    rw [hs]
    have he : List.replicate n (none : Option (CompCell A B)) ++ none :: left =
        none :: (List.replicate n none ++ left) := by
      calc
        _ = (List.replicate n none ++ [none]) ++ left := by simp
        _ = List.replicate (n + 1) none ++ left := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ]; rfl
    simpa only [TM.run, Function.iterate_succ_apply, he, List.tail_cons, List.headD_cons]
      using ih (none :: left)

#print axioms solution
