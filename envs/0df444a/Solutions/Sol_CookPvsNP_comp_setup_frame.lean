-- Prove2me | solution 1 for CookPvsNP.comp_setup_frame
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:35:50.252337+00:00
-- url     : https://prove2.me/submissions/2cf7b5c6-5d41-45f7-aab1-4d90345295c1

import Definitions.Def_CookPvsNP_CompFrames

set_option autoImplicit false

open CookPvsNP

private theorem run_add {Γ : Type} (M : TM Γ) (a b : ℕ) (c : Cfg Γ M.Q) :
    M.run (a + b) c = M.run a (M.run b c) := Function.iterate_add_apply _ _ _ _

section
variable {I S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (ι : I ↪ Γ₁) (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)

local notation "C" => compTM j₁ j₂ M₁ M₂
local notation "embed" => compInputEmbedding (Γ₂ := Γ₂) ι

private theorem scan (xs : List I) (left : List (Option (CompCell Γ₁ Γ₂))) :
    (C).run xs.length ⟨.setupScan, left, (xs.map (some ∘ embed)).headD none,
      (xs.map (some ∘ embed)).tail⟩ =
    ⟨.setupScan, (xs.map (some ∘ embed)).reverse ++ left, none, []⟩ := by
  induction xs generalizing left with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply]
    have hs : (C).step ⟨.setupScan, left, some (embed x), xs.map (some ∘ embed)⟩ =
        ⟨.setupScan, some (embed x) :: left, (xs.map (some ∘ embed)).headD none,
          (xs.map (some ∘ embed)).tail⟩ := by
      simp [TM.step, TM.IsHalting, compTM, CompCell.unpack, CompCell.pack,
        compInputEmbedding]
    simp only [List.map_cons, List.headD_cons, List.tail_cons, Function.comp_apply]
    rw [hs]
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (some (embed x) :: left)

private theorem return_step (x : I) (left right : List (Option (CompCell Γ₁ Γ₂))) :
    (C).step ⟨.setupReturn, left, some (embed x), right⟩ =
      ⟨.setupReturn, left.tail, left.headD none, some (embed x) :: right⟩ := by
  cases left <;> simp [TM.step, TM.IsHalting, compTM, CompCell.unpack, CompCell.pack,
    compInputEmbedding]

private theorem return_past (xs : List I) (origin : Option (CompCell Γ₁ Γ₂))
    (right : List (Option (CompCell Γ₁ Γ₂))) :
    (C).run xs.length ⟨.setupReturn, (xs.map (some ∘ embed) ++ [origin]).tail,
      (xs.map (some ∘ embed) ++ [origin]).headD none, right⟩ =
    ⟨.setupReturn, [], origin, (xs.map (some ∘ embed)).reverse ++ right⟩ := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply,
      List.map_cons, List.cons_append, List.headD_cons, List.tail_cons, Function.comp_apply]
    rw [return_step ι j₁ j₂ M₁ M₂]
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (some (embed x) :: right)

private theorem blank_step (left : List (Option (CompCell Γ₁ Γ₂))) :
    (C).step ⟨.setupScan, left, none, []⟩ =
      ⟨.setupReturn, left.tail, left.headD none,
        [some { CompCell.blank with rightB := true }]⟩ := by
  cases left <;> simp [TM.step, TM.IsHalting, compTM, CompCell.unpack,
    CompCell.pack, CompCell.blank]

private theorem finish (x : I) (r : Option (CompCell Γ₁ Γ₂))
    (rs : List (Option (CompCell Γ₁ Γ₂)))
    (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run 2 ⟨.setupReturn, [], some { (embed x) with setupOrigin := true }, r :: rs⟩ =
      ⟨.sim₁ M₁.q₀, [], some (embed x), r :: rs⟩ := by
  simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
    CompCell.unpack, CompCell.pack, compInputEmbedding]
  constructor
  · rfl
  · simpa [CompCell.pack, CompCell.unpack] using hr

/-- Exact setup configuration, including the sentinel just beyond the input.
For empty input the sentinel is one cell to the right of the initial head. -/
private theorem setup_raw (w : List I) :
    (C).run (2 * max w.length 1 + 2) ((C).init (w.map embed)) =
      ⟨.sim₁ M₁.q₀, [], (w.map (some ∘ embed)).headD none,
        (w.map (some ∘ embed)).tail ++ [some { CompCell.blank with rightB := true }]⟩ := by
  cases w with
  | nil =>
    simp [TM.run, TM.init, Function.iterate_succ_apply, TM.step, TM.IsHalting,
      compTM, CompCell.unpack, CompCell.pack, CompCell.blank]
  | cons x xs =>
    let origin : Option (CompCell Γ₁ Γ₂) := some { (embed x) with setupOrigin := true }
    let marker : Option (CompCell Γ₁ Γ₂) := some { CompCell.blank with rightB := true }
    have hs : (C).run 1 ((C).init ((x :: xs).map embed)) =
        ⟨.setupScan, [origin], (xs.map (some ∘ embed)).headD none,
          (xs.map (some ∘ embed)).tail⟩ := by
      simp [TM.run, TM.init, TM.step, TM.IsHalting, compTM, origin,
        CompCell.unpack, CompCell.pack, compInputEmbedding, List.map_map, Function.comp_def]
    have hb : (C).run 1 ⟨.setupScan, (xs.map (some ∘ embed)).reverse ++ [origin], none, []⟩ =
        ⟨.setupReturn, ((xs.map (some ∘ embed)).reverse ++ [origin]).tail,
          ((xs.map (some ∘ embed)).reverse ++ [origin]).headD none, [marker]⟩ := by
      exact blank_step j₁ j₂ M₁ M₂ _
    have hr := return_past ι j₁ j₂ M₁ M₂ xs.reverse origin [marker]
    simp only [List.length_reverse, List.map_reverse, List.reverse_reverse] at hr
    have hf : (C).run 2 ⟨.setupReturn, [], origin, xs.map (some ∘ embed) ++ [marker]⟩ =
        ⟨.sim₁ M₁.q₀, [], some (embed x), xs.map (some ∘ embed) ++ [marker]⟩ := by
      cases xs with
      | nil =>
        exact finish ι j₁ j₂ M₁ M₂ x marker []
          (by simp [marker, CompCell.unpack, CompCell.pack, CompCell.blank])
      | cons y ys =>
        exact finish ι j₁ j₂ M₁ M₂ x (some (embed y)) (ys.map (some ∘ embed) ++ [marker])
          (by simp [CompCell.unpack, CompCell.pack, compInputEmbedding])
    rw [show 2 * max (x :: xs).length 1 + 2 =
        2 + (xs.length + (1 + (xs.length + 1))) by simp; omega]
    rw [run_add, run_add, run_add, run_add, hs, scan ι j₁ j₂ M₁ M₂, hb, hr]
    simpa [origin, marker] using hf

end

theorem solution {I S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (ι : I ↪ Γ₁) (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (w : List I) :
    (compTM j₁ j₂ M₁ M₂).run (2 * max w.length 1 + 2)
      ((compTM j₁ j₂ M₁ M₂).init (w.map (compInputEmbedding ι))) =
      compFirstCfg (M₁.init (w.map ι)) := by
  rw [setup_raw ι j₁ j₂ M₁ M₂ w]
  cases w <;>
    simp [TM.init, compFirstCfg, CompCell.firstSymbol, CompCell.plain, CompCell.pack,
      compInputEmbedding, List.map_map, Function.comp_def, CompCell.rightMarker, CompCell.blank] <;> rfl

#print axioms solution
