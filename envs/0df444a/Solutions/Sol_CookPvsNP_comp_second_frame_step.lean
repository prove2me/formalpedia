-- Prove2me | solution 1 for CookPvsNP.comp_second_frame_step
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:54:21.758387+00:00
-- url     : https://prove2.me/submissions/fa440ec3-dd68-4ae6-a3a9-e2b3823368f3

import Definitions.Def_CookPvsNP_CompSecondFrame

set_option autoImplicit false

open CookPvsNP

private theorem unpack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.unpack (CompCell.plain a b) = ⟨a, b, false, false, false, false, false⟩ := by
  cases a <;> cases b <;> simp [CompCell.plain, CompCell.pack, CompCell.unpack, CompCell.blank]

private theorem pack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.pack (⟨a, b, false, false, false, false, false⟩ : CompCell A B) =
      CompCell.plain a b := rfl

private theorem unpack_left {A B : Type} (a : Option A) :
    CompCell.unpack (CompCell.leftMarker (Γ₂ := B) a) =
      ⟨a, none, false, true, false, false, false⟩ := rfl

private theorem pack_left {A B : Type} (a : Option A) :
    CompCell.pack (⟨a, none, false, true, false, false, false⟩ : CompCell A B) =
      CompCell.leftMarker a := by simp [CompCell.pack, CompCell.leftMarker, CompCell.blank]

private theorem unpack_right {A B : Type} :
    CompCell.unpack (CompCell.rightMarker : Option (CompCell A B)) =
      ⟨none, none, false, false, true, false, false⟩ := rfl

private theorem pack_right {A B : Type} :
    CompCell.pack (⟨none, none, false, false, true, false, false⟩ : CompCell A B) =
      CompCell.rightMarker := rfl

private theorem unpack_none {A B : Type} :
    CompCell.unpack (none : Option (CompCell A B)) =
      ⟨none, none, false, false, false, false, false⟩ := rfl

private theorem plain_none {A B : Type} :
    CompCell.plain (none : Option A) (none : Option B) = none := rfl

private theorem source_step {A B : Type} (M : TM B) (c : CompSecondFrame A B M.Q) :
    (c.step M).source = M.step c.source := by
  rcases c with ⟨q, left, head, right, mark, garbage, padding⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [CompSecondFrame.step, CompSecondFrame.source, TM.step, TM.IsHalting, hq]
  · rcases hd : M.δ q head.2 with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;>
      simp [CompSecondFrame.step, CompSecondFrame.source, TM.step, TM.IsHalting, hq, hd]

/-- The decorated frame follows the second source machine exactly, and each
nonhalting source step takes three transitions of the original composite machine. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : CompSecondFrame Γ₁ Γ₂ M₂.Q) :
    (c.step M₂).source = M₂.step c.source ∧
    (¬ M₂.IsHalting c.source →
      (compTM j₁ j₂ M₁ M₂).run 3 c.encode = (c.step M₂).encode) := by
  refine ⟨source_step M₂ c, ?_⟩
  intro hn
  rcases c with ⟨q, left, head, right, mark, garbage, padding⟩
  have hq : ¬ (q = M₂.qaccept ∨ q = M₂.qreject) := hn
  rcases hd : M₂.δ q head.2 with ⟨q', w, move⟩
  cases move with
  | left =>
    cases left with
    | nil =>
      cases garbage <;>
        simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
          TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
          unpack_plain, pack_plain, unpack_left, pack_left, unpack_right, pack_right,
          unpack_none, plain_none, CompCell.firstSymbol, hq, hd]
    | cons a left =>
      simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
        TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
        unpack_plain, pack_plain, unpack_left, pack_left, unpack_right, pack_right,
        unpack_none, plain_none, CompCell.firstSymbol, hq, hd]
  | right =>
    cases right with
    | nil =>
      cases padding <;>
        simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
          TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
          unpack_plain, pack_plain, unpack_left, pack_left, unpack_right, pack_right,
          unpack_none, plain_none, CompCell.firstSymbol, List.replicate_succ, hq, hd]
    | cons a right =>
      simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
        TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
        unpack_plain, pack_plain, unpack_left, pack_left, unpack_right, pack_right,
        unpack_none, plain_none, CompCell.firstSymbol, hq, hd]

#print axioms solution
