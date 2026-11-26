-- Prove2me | solution 1 for CategoryTheory.SequentialSystem.epi_transition_of_epi_app
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:16.752708+00:00
-- url     : https://prove2.me/submissions/0ae4327b-1552-4e54-96fc-fe0fae753be6

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Inverse systems indexed by `ℕᵒᵖ`

We study functors `F : ℕᵒᵖ ⥤ C` ("inverse systems") in a category `C` with zero object
and zero morphisms. The *transition maps* of `F` are the maps
`F.obj (op (n + 1)) ⟶ F.obj (op n)`.

The key results concern injective objects of the functor category:

- `CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective`: the transition
  maps of an injective inverse system are split epimorphisms.
- `CategoryTheory.SequentialSystem.injective_obj_of_injective`: the objects of an
  injective inverse system are injective.

Both are proved using the "extension by zero" systems `extendSystem n M`, which take the
value `M` in degrees `≤ n` (with identity transitions) and `0` above, together with the
natural identification `(extendSystem n M ⟶ F) ≃ (M ⟶ F.obj (op n))` and the
monomorphism `extendSystem n M ⟶ extendSystem (n + 1) M`.

We also record stability properties of the class of systems with epimorphic transition
maps.
-/

universe w v v' u u'

open CategoryTheory Limits Opposite

open scoped ZeroObject

namespace CategoryTheory
namespace SequentialSystem

variable {C : Type u} [Category.{v} C]

section Transition


/-- Transition maps of quotients of systems with epimorphic transitions are epimorphisms:
if `τ : F ⟶ G` is a levelwise epimorphism and `F` has epimorphic transition maps, then so
does `G`. -/
lemma epi_transition_of_epi_app {F G : ℕᵒᵖ ⥤ C} (τ : F ⟶ G)
    (hτ : ∀ k, Epi (τ.app k)) (hF : ∀ n, Epi (transition F n)) (n : ℕ) :
    Epi (transition G n) := by
  have hnat : transition F n ≫ τ.app (op n) = τ.app (op (n + 1)) ≫ transition G n :=
    τ.naturality (homOfLE (Nat.le_succ n)).op
  haveI := hF n
  haveI := hτ (op n)
  haveI : Epi (τ.app (op (n + 1)) ≫ transition G n) := by
    rw [← hnat]
    exact epi_comp _ _
  exact epi_of_epi (τ.app (op (n + 1))) _


end Transition


end SequentialSystem
end CategoryTheory


theorem solution.{sol_u1, sol_u2} : type_of% @CategoryTheory.SequentialSystem.epi_transition_of_epi_app.{sol_u1, sol_u2} := @CategoryTheory.SequentialSystem.epi_transition_of_epi_app.{sol_u1, sol_u2}
