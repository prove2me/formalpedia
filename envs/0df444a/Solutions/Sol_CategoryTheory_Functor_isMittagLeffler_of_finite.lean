-- Prove2me | solution 1 for CategoryTheory.Functor.isMittagLeffler_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:07.858796+00:00
-- url     : https://prove2.me/submissions/314837e8-2135-4fea-917d-80ffed526dc0

import Mathlib.CategoryTheory.CofilteredSystem

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# The Mittag-Leffler condition for `ℕᵒᵖ`-indexed systems

We specialize `CategoryTheory.Functor.IsMittagLeffler` to inverse systems indexed by
`ℕᵒᵖ`, where it takes the familiar form: for every level `n` there is an `m ≥ n` such
that the image of every level `k` in level `n` contains the image of level `m`
(`CategoryTheory.Functor.isMittagLeffler_nat_iff`).

We also record that a functor with finite values satisfies the Mittag-Leffler
condition (`CategoryTheory.Functor.isMittagLeffler_of_finite`) and that the
Mittag-Leffler condition descends along a levelwise bijective natural transformation
(`CategoryTheory.Functor.IsMittagLeffler.of_natTrans_bijective`).
-/

universe w v u

open Set

namespace CategoryTheory
namespace Functor

/-- A functor with finite values satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler_of_finite {J : Type u} [Category.{w} J] [IsCofilteredOrEmpty J]
    (F : J ⥤ Type v) [∀ j, Finite (F.obj j)] : F.IsMittagLeffler :=
  F.isMittagLeffler_of_exists_finite_range fun j ↦ ⟨j, 𝟙 j, Set.toFinite _⟩


variable (F : ℕᵒᵖ ⥤ Type v)


end Functor
end CategoryTheory


theorem solution.{sol_u1, sol_u2, sol_u3} : type_of% @CategoryTheory.Functor.isMittagLeffler_of_finite.{sol_u1, sol_u2, sol_u3} := @CategoryTheory.Functor.isMittagLeffler_of_finite.{sol_u1, sol_u2, sol_u3}
