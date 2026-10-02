-- Prove2me | solution 1 for CookPvsNP.comp_cleanup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:41.787811+00:00
-- url     : https://prove2.me/submissions/bae5c035-dc7f-49ce-b2f0-2679489b8175

import Definitions.Def_CookPvsNP_CompCleanup

set_option autoImplicit false

open CookPvsNP

private theorem unpack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.unpack (CompCell.plain a b) = ⟨a, b, false, false, false, false, false⟩ := by
  cases a <;> cases b <;> simp [CompCell.plain, CompCell.pack, CompCell.unpack, CompCell.blank]

private theorem pack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.pack (⟨a, b, false, false, false, false, false⟩ : CompCell A B) =
      CompCell.plain a b := rfl

private theorem plain_none {A B : Type} :
    CompCell.plain (none : Option A) (none : Option B) = none := rfl

private theorem unpack_final {A B : Type} (b : Option B) :
    CompCell.unpack (CompCell.finalMarker (Γ₁ := A) b) =
      ⟨none, b, false, false, false, false, true⟩ := rfl

private theorem pack_final {A B : Type} (b : Option B) :
    CompCell.pack (⟨none, b, false, false, false, false, true⟩ : CompCell A B) =
      CompCell.finalMarker b := by simp [CompCell.pack, CompCell.finalMarker]

private theorem unpack_right {A B : Type} :
    CompCell.unpack (CompCell.rightMarker : Option (CompCell A B)) =
      ⟨none, none, false, false, true, false, false⟩ := rfl

private theorem unpack_none {A B : Type} :
    CompCell.unpack (none : Option (CompCell A B)) =
      ⟨none, none, false, false, false, false, false⟩ := rfl

private theorem run_add {Γ : Type} (M : TM Γ) (a b : ℕ) (c : Cfg Γ M.Q) :
    M.run (a + b) c = M.run a (M.run b c) := Function.iterate_add_apply _ _ _ _

section
variable {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
local notation "C" => compTM j₁ j₂ M₁ M₂

private theorem clean_step (ended : Bool) (a : Option A) (b : Option B)
    (left right : List (Option (CompCell A B))) :
    (C).step ⟨.finalClean ended, left, CompCell.plain a b, right⟩ =
      ⟨.finalClean (ended || b.isNone), CompCell.secondSymbol (if ended then none else b) :: left,
        right.headD none, right.tail⟩ := by
  cases ended <;> cases b <;>
    simp [TM.step, TM.IsHalting, compTM, unpack_plain, pack_plain, plain_none, CompCell.secondSymbol]

private theorem scan (xs : List (Option A × Option B)) (ended : Bool)
    (left : List (Option (CompCell A B))) (padding : ℕ) :
    ∃ ended', (C).run xs.length
      ⟨.finalClean ended, left,
        (xs.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate padding none).headD none,
        (xs.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate padding none).tail⟩ =
      ⟨.finalClean ended', ((compCleanTail ended (xs.map Prod.snd)).map CompCell.secondSymbol).reverse ++ left,
        CompCell.rightMarker, List.replicate padding none⟩ := by
  induction xs generalizing ended left with
  | nil => exact ⟨ended, rfl⟩
  | cons p xs ih =>
    obtain ⟨e, h⟩ := ih (ended || p.2.isNone)
      (CompCell.secondSymbol (if ended then none else p.2) :: left)
    refine ⟨e, ?_⟩
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    rw [clean_step j₁ j₂ M₁ M₂]
    simpa [TM.run, compCleanTail, List.reverse_cons, List.append_assoc] using h

private theorem return_step (b : Option B) (left right : List (Option (CompCell A B))) :
    (C).step ⟨.finalReturn, left, CompCell.secondSymbol b, right⟩ =
      ⟨.finalReturn, left.tail, left.headD none, CompCell.secondSymbol b :: right⟩ := by
  cases left <;>
    simp [TM.step, TM.IsHalting, compTM, CompCell.secondSymbol, unpack_plain, pack_plain]

private theorem return_past (xs : List (Option B)) (origin : Option (CompCell A B))
    (left right : List (Option (CompCell A B))) :
    (C).run xs.length ⟨.finalReturn, (xs.map CompCell.secondSymbol ++ [origin]).tail ++ left,
      (xs.map CompCell.secondSymbol ++ [origin]).headD none, right⟩ =
      ⟨.finalReturn, left, origin, (xs.map CompCell.secondSymbol).reverse ++ right⟩ := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    rw [return_step j₁ j₂ M₁ M₂]
    cases xs <;> simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih (CompCell.secondSymbol x :: right)

private theorem finish (b : Option B) (left : List (Option (CompCell A B)))
    (r : Option (CompCell A B)) (rs : List (Option (CompCell A B)))
    (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run 2 ⟨.finalReturn, left, CompCell.finalMarker b, r :: rs⟩ =
      ⟨.haltAccept, left, CompCell.secondSymbol b, r :: rs⟩ := by
  simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
    unpack_final, pack_plain, CompCell.secondSymbol, hr]

/-- Exact configuration and exact transition count of the original final cleanup. -/
private theorem cleanup_raw (c : CompSecondFrame A B M₂.Q) (hn : M₂.IsHalting c.source) :
    (C).run (2 * c.right.length + 4) c.encode = compCleanCfg c := by
  let L := (CompSecondFrame.encode (Q₁ := M₁.Q) c).left
  let origin : Option (CompCell A B) := CompCell.finalMarker c.head.2
  let out := compCleanTail c.head.2.isNone (c.right.map Prod.snd)
  have hq : c.state = M₂.qaccept ∨ c.state = M₂.qreject := hn
  have hs : (C).run 1 c.encode =
      ⟨.finalClean c.head.2.isNone, origin :: L,
        (c.right.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate c.padding none).headD none,
        (c.right.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate c.padding none).tail⟩ := by
    simp [TM.run, TM.step, TM.IsHalting, compTM, CompSecondFrame.encode, origin, L,
      unpack_plain, pack_final, hq]
  obtain ⟨e, hscan⟩ := scan j₁ j₂ M₁ M₂ c.right c.head.2.isNone (origin :: L) c.padding
  have hb : (C).run 1 ⟨.finalClean e, (out.map CompCell.secondSymbol).reverse ++ origin :: L,
      CompCell.rightMarker, List.replicate c.padding none⟩ =
      ⟨.finalReturn, ((out.map CompCell.secondSymbol).reverse ++ [origin]).tail ++ L,
        ((out.map CompCell.secondSymbol).reverse ++ [origin]).headD none,
        List.replicate (c.padding + 1) none⟩ := by
    cases ho : (out.map (CompCell.secondSymbol (Γ₁ := A))).reverse <;>
      simp [TM.run, TM.step, TM.IsHalting, compTM, unpack_right, List.replicate_succ]
  have hr := return_past j₁ j₂ M₁ M₂ out.reverse origin L (List.replicate (c.padding + 1) none)
  have hlen : out.length = c.right.length := by
    dsimp [out]
    generalize c.head.2.isNone = b
    induction c.right generalizing b <;> simp [compCleanTail, *]
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse, hlen] at hr
  have hf : (C).run 2 ⟨.finalReturn, L, origin,
      out.map CompCell.secondSymbol ++ List.replicate (c.padding + 1) none⟩ = compCleanCfg c := by
    cases ho : out with
    | nil =>
      have h := finish j₁ j₂ M₁ M₂ c.head.2 L none (List.replicate c.padding none) rfl
      simp [compCleanCfg, out, origin, L, List.replicate_succ, ho] at h ⊢
      exact h
    | cons x xs =>
      have hp : CompCell.pack (CompCell.unpack (CompCell.secondSymbol (Γ₁ := A) x)) =
          CompCell.secondSymbol (Γ₁ := A) x := by rw [CompCell.secondSymbol, unpack_plain, pack_plain]
      have h := finish j₁ j₂ M₁ M₂ c.head.2 L (CompCell.secondSymbol x)
        (xs.map CompCell.secondSymbol ++ List.replicate (c.padding + 1) none) hp
      simp [compCleanCfg, out, origin, L, ho] at h ⊢
      exact h
  rw [show 2 * c.right.length + 4 = 2 + (c.right.length + (1 + (c.right.length + 1))) by omega]
  unfold TM.run at hs hscan hb hr hf ⊢
  dsimp only [compTM] at hs hscan hb hr hf ⊢
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_add_apply, hs, hscan, hb, hr]
  exact hf

end

theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : CompSecondFrame A B M₂.Q) (hn : M₂.IsHalting c.source) :
    (compTM j₁ j₂ M₁ M₂).run (2 * c.right.length + 4) c.encode = compCleanCfg c := by
  exact cleanup_raw j₁ j₂ M₁ M₂ c hn

#print axioms solution
