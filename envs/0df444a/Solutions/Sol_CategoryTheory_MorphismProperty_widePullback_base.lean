-- Prove2me | solution 1 for CategoryTheory.MorphismProperty.widePullback_base
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b6e7ebb2-036d-5eeb-b5e3-098ef8e90d32

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_MorphismProperty_widePullback_base

set_option autoImplicit false

universe v u

p2m_open "CategoryTheory P2MW.S_CategoryTheory_MorphismProperty_widePullback_base.CategoryTheory CategoryTheory.Limits P2MW.S_CategoryTheory_MorphismProperty_widePullback_base.CategoryTheory.Limits"

namespace CategoryTheory
p2m_export "CategoryTheory" "Category MorphismProperty inv over IsIso"
namespace Limits
p2m_export "CategoryTheory.Limits" "WidePullback.lift_π pullback.hom_ext WidePullback.lift_base_assoc WidePullback.lift_base HasPullbacks pullback.condition pullback WidePullback.lift_π_assoc WidePullback.π WidePullback.hom_ext pullback.snd WidePullback.π_arrow WidePullback.base widePullback WidePullback.lift HasFiniteWidePullbacks pullback.lift pullback.fst"
namespace WidePullback
p2m_export "CategoryTheory.Limits.WidePullback" "lift_π lift_base_assoc lift_base lift_π_assoc π hom_ext π_arrow base lift"
p2m_open "CategoryTheory.Limits.WidePullback CategoryTheory.Limits CategoryTheory"

attribute [local simp] WidePullback.lift_π WidePullback.lift_base WidePullback.lift_π_assoc
  WidePullback.lift_base_assoc

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]

omit [HasPullbacks C] in

theorem isIso_base_of_isEmpty {J : Type} [Finite J] [IsEmpty J] {S : C} (X : J → C)
    (f : ∀ j, X j ⟶ S) : IsIso (WidePullback.base f) :=
  ⟨⟨WidePullback.lift (𝟙 S) (fun j => isEmptyElim j) (fun j => isEmptyElim j),
    by
      apply WidePullback.hom_ext
      · intro j; exact isEmptyElim j
      · simp,
    by simp⟩⟩

set_option backward.isDefEq.respectTransparency false in

noncomputable def succIsoPullback {S : C} {r : ℕ} (X : Fin (r + 1) → C) (f : ∀ i, X i ⟶ S) :
    widePullback S X f ≅
      pullback (f 0) (WidePullback.base fun i : Fin r => f i.succ) where
  hom := pullback.lift (WidePullback.π f 0)
    (WidePullback.lift (WidePullback.base f) (fun i => WidePullback.π f i.succ)
      (fun i => WidePullback.π_arrow f i.succ))
    (by simp [WidePullback.π_arrow])
  inv := WidePullback.lift
    (pullback.snd _ _ ≫ WidePullback.base fun i : Fin r => f i.succ)
    (fun j => Fin.cases (pullback.fst _ _)
      (fun i => pullback.snd _ _ ≫ WidePullback.π (fun i : Fin r => f i.succ) i) j)
    (fun j => by
      cases j using Fin.cases with
      | zero => simpa using pullback.condition
      | succ i => simp [WidePullback.π_arrow])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      cases j using Fin.cases with
      | zero => simp
      | succ i => simp
    · simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · apply WidePullback.hom_ext
      · intro i; simp
      · simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem succIsoPullback_hom_snd_base {S : C} {r : ℕ} (X : Fin (r + 1) → C) (f : ∀ i, X i ⟶ S) :
    (succIsoPullback X f).hom ≫ pullback.snd _ _ ≫ (WidePullback.base fun i : Fin r => f i.succ) =
      WidePullback.base f := by
  simp [succIsoPullback]

end CategoryTheory.Limits.WidePullback

namespace CategoryTheory
p2m_export "CategoryTheory" "Category MorphismProperty inv over IsIso"
namespace MorphismProperty
p2m_export "CategoryTheory.MorphismProperty" "pullback_snd IsStableUnderBaseChange over IsMultiplicative pullbacks cancel_left_of_respectsIso under of_isIso comp_mem"
p2m_open "CategoryTheory.MorphismProperty CategoryTheory"

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]

theorem widePullback_base_aux {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} : ∀ {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S), (∀ i, P (f i)) →
      P (WidePullback.base f)
  | 0, X, f, _ => by
    have := WidePullback.isIso_base_of_isEmpty X f
    exact P.of_isIso _
  | r + 1, X, f, hf => by
    rw [← WidePullback.succIsoPullback_hom_snd_base X f, P.cancel_left_of_respectsIso]
    exact P.comp_mem _ _ (P.pullback_snd _ _ (hf 0))
      (widePullback_base_aux (fun i => X i.succ) (fun i => f i.succ) fun i => hf i.succ)

end CategoryTheory.MorphismProperty

theorem solution
    {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
    {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S) (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) :=
  CategoryTheory.MorphismProperty.widePullback_base_aux X f hf

end S_CategoryTheory_MorphismProperty_widePullback_base
end P2MW
export P2MW.S_CategoryTheory_MorphismProperty_widePullback_base (solution)
