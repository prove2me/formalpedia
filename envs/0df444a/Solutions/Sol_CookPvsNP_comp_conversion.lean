-- Prove2me | solution 1 for CookPvsNP.comp_conversion
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:29:30.318088+00:00
-- url     : https://prove2.me/submissions/1ee0cc82-161c-4c0a-8c08-f7291d1a5661

import Theorems.Thm_CookPvsNP_comp_conversion_entry
import Theorems.Thm_CookPvsNP_comp_conversion_copy
import Theorems.Thm_CookPvsNP_comp_conversion_boundary
import Theorems.Thm_CookPvsNP_comp_cell_laws

set_option autoImplicit false
open CookPvsNP

/-- The entire conversion phase implements the intermediate alphabet translation. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (q : M₁.Q) (left : List (Option A)) (w : List S) (padding : ℕ)
    (hn : q = M₁.qaccept ∨ q = M₁.qreject) :
    (compTM j₁ j₂ M₁ M₂).run
      (2 * (compWordCfg j₁ q left w padding).right.length + 6)
      (compFirstCfg (compWordCfg j₁ q left w padding)) =
      (compConvertedFrame j₁ j₂ M₂.q₀ left w padding).encode := by
  let C := compTM j₁ j₂ M₁ M₂
  let L := CompCell.leftMarker (left.headD none) :: left.tail.map (CompCell.firstSymbol (Γ₂ := B))
  have hblank : CompCell.firstSymbol (Γ₁ := A) (Γ₂ := B) none = none := rfl
  have he := comp_conversion_entry j₁ j₂ M₁ M₂ (compWordCfg j₁ q left w padding) hn
  cases w with
  | nil =>
    have hs : C.run 1 ⟨.convCopy true, L, CompCell.originSymbol none none,
        List.replicate padding none ++ [CompCell.rightMarker]⟩ =
        ⟨.convEmptyRight, CompCell.originSymbol none none :: L,
          (List.replicate padding none ++ [CompCell.rightMarker]).headD none,
          (List.replicate padding none ++ [CompCell.rightMarker]).tail⟩ := by
      simp [C, TM.run, TM.step, TM.IsHalting, compTM, CompCell.originSymbol,
        CompCell.pack, CompCell.unpack]
    have hb := comp_conversion_boundary j₁ j₂ M₁ M₂ [] (by simp) none none L padding true
    simp only [compWordCfg, List.map_nil, List.headD_nil, List.tail_nil, List.nil_append,
      List.map_replicate, hblank] at he
    simp only [compWordCfg, List.map_nil, List.headD_nil, List.tail_nil, List.nil_append,
      List.length_replicate]
    rw [show 2 * padding + 6 = (0 + 2 * padding + 3) + (1 + 2) by omega]
    unfold TM.run at he hs hb ⊢
    dsimp only [C, compTM] at he hs hb ⊢
    rw [Function.iterate_add_apply _ (0 + 2 * padding + 3) (1 + 2),
      Function.iterate_add_apply _ 1 2, he, hs]
    simpa only [List.length_nil, List.map_nil, List.nil_append, List.reverse_nil, List.headD_nil,
      List.tail_nil, Bool.true_eq, ↓reduceIte, compConvertedFrame, CompSecondFrame.encode,
      List.singleton_append, L] using hb
  | cons a xs =>
    let cell (x : S) : CompCell A B := ⟨some (j₁ x), some (j₂ x), false, false, false, false, false⟩
    let R := List.replicate padding (none : Option (CompCell A B)) ++ [CompCell.rightMarker]
    have hm : xs.map (fun x => CompCell.plain (some (j₁ x)) (some (j₂ x))) =
        (xs.map cell).map CompCell.pack := by rw [List.map_map]; rfl
    have hs : C.run 1
        ⟨.convCopy true, L, CompCell.originSymbol (some (j₁ a)) none,
          xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ R⟩ =
        ⟨.convCopy false, CompCell.originSymbol (some (j₁ a)) (some (j₂ a)) :: L,
          (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ R).headD none,
          (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ R).tail⟩ := by
      simp [C, TM.run, TM.step, TM.IsHalting, compTM, CompCell.originSymbol,
        CompCell.pack, CompCell.unpack, (comp_cell_laws j₁ j₂).2.2]
    have hc := comp_conversion_copy j₁ j₂ M₁ M₂ xs
      (CompCell.originSymbol (some (j₁ a)) (some (j₂ a)) :: L) R
    have hx : ∀ x ∈ (xs.map cell).reverse, x.secondOrigin = false := by
      intro x h
      simp only [List.mem_reverse, List.mem_map] at h
      obtain ⟨y, _, rfl⟩ := h
      rfl
    have hb := comp_conversion_boundary j₁ j₂ M₁ M₂ (xs.map cell).reverse hx
      (some (j₁ a)) (some (j₂ a)) L padding false
    simp only [List.length_reverse, List.length_map, List.map_reverse, List.reverse_reverse,
      Bool.false_eq_true, ↓reduceIte, ← hm] at hb
    simp only [compWordCfg, List.map_cons, List.headD_cons, List.tail_cons,
      List.map_append, List.map_replicate, List.map_map, Function.comp_def, hblank,
      List.append_assoc] at he
    simp only [compWordCfg, List.map_cons, List.headD_cons, List.tail_cons, List.length_append,
      List.length_map, List.length_replicate, Function.comp_def]
    rw [show 2 * (xs.length + padding) + 6 =
      (xs.length + 2 * padding + 3) + (xs.length + (1 + 2)) by omega]
    unfold TM.run at he hs hc hb ⊢
    dsimp only [C, compTM] at he hs hc hb ⊢
    rw [Function.iterate_add_apply _ (xs.length + 2 * padding + 3) (xs.length + (1 + 2)),
      Function.iterate_add_apply _ xs.length (1 + 2), Function.iterate_add_apply _ 1 2,
      he, hs, hc]
    have hresult := hb
    simp only [compConvertedFrame, CompSecondFrame.encode, List.map_cons, List.headD_cons,
      List.tail_cons, List.map_nil, List.nil_append, List.map_map, Function.comp_def,
      List.singleton_append, List.append_assoc, L, R] at hresult ⊢
    exact hresult

#print axioms solution
