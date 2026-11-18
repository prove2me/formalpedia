-- Prove2me | solution 1 for CallCountPOPBR.Supplement.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:22:45.784955+00:00
-- url     : https://prove2.me/submissions/4104e19f-bc5c-41eb-a163-d0dcee3d6a79

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_RecProc

set_option autoImplicit false

namespace CC41Aux
open CallCountPOPBR.Supplement

universe u

lemma count_eq {X : Type u} (P : RecProc X) (x : X) :
    P.count x = 1 + ((P.ch x).map P.count).sum := by
  unfold RecProc.count
  rw [WellFounded.fix_eq]
  congr 2
  conv_rhs => rw [← List.attach_map_subtype_val (P.ch x), List.map_map]
  rfl

lemma sum_affine {X : Type u} (l : List X) (V : X → ℝ) (a b : ℝ) :
    (l.map (fun y => a * V y + b)).sum = a * (l.map V).sum + l.length * b := by
  induction l with
  | nil => simp
  | cons y l ih => simp [ih]; ring

lemma count_cast {X : Type u} (P : RecProc X) (x : X) :
    (P.count x : ℝ) = 1 + ((P.ch x).map (fun y => (P.count y : ℝ))).sum := by
  rw [count_eq]; push_cast; rw [List.map_map]; rfl

end CC41Aux

universe u

open CallCountPOPBR.Supplement in
theorem solution {X : Type u} (P : RecProc X) (V : X → ℝ) (a b : ℝ) (ha : a ≠ 0) :
    (∀ x, (P.count x : ℝ) = a * V x + b) ↔
      ((∀ x, P.ch x = [] → a * V x + b = 1) ∧
       (∀ x, P.ch x ≠ [] →
          a * (V x - ((P.ch x).map V).sum) = 1 + (((P.ch x).length : ℝ) - 1) * b)) := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x _ => ?_⟩
    · rw [← h x, CC41Aux.count_cast, hx]; simp
    · have e := CC41Aux.count_cast P x
      rw [h x, List.map_congr_left (fun y _ => h y), CC41Aux.sum_affine] at e
      linarith
  · rintro ⟨hleaf, hint⟩ x
    induction x using P.wf.induction with
    | _ x ih =>
      rw [CC41Aux.count_cast, List.map_congr_left (fun y hy => ih y hy), CC41Aux.sum_affine]
      by_cases hx : P.ch x = []
      · have := hleaf x hx
        rw [hx]; simp; linarith
      · have := hint x hx
        linarith
