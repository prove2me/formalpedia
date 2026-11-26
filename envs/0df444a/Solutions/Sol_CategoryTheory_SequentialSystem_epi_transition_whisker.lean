-- Prove2me | solution 1 for CategoryTheory.SequentialSystem.epi_transition_whisker
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T17:04:06.145672+00:00
-- url     : https://prove2.me/submissions/f3b1d08d-b658-43bb-ad24-d994cd6d173b

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


/-- Whiskering with a functor preserving epimorphisms preserves epimorphic transitions. -/
lemma epi_transition_whisker {D : Type u'} [Category.{v'} D] {F : ℕᵒᵖ ⥤ C} (L : C ⥤ D)
    [L.PreservesEpimorphisms] (hF : ∀ n, Epi (transition F n)) (n : ℕ) :
    Epi (transition (F ⋙ L) n) :=
  L.map_epi _


end Transition


end SequentialSystem
end CategoryTheory


theorem solution.{sol_u1, sol_u2, sol_u3, sol_u4} : type_of% @CategoryTheory.SequentialSystem.epi_transition_whisker.{sol_u1, sol_u2, sol_u3, sol_u4} := @CategoryTheory.SequentialSystem.epi_transition_whisker.{sol_u1, sol_u2, sol_u3, sol_u4}
