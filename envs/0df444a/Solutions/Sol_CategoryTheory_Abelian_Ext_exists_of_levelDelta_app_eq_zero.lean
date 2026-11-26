-- Prove2me | solution 1 for CategoryTheory.Abelian.Ext.exists_of_levelDelta_app_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:41:32.626855+00:00
-- url     : https://prove2.me/submissions/1f14d737-808c-4e6c-912c-47e372c17542

import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_SequentialLimit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# `Ext` out of a constant system versus the limit of levelwise `Ext`-groups

Let `A` be an abelian category with enough injectives and countable products, and let
`Z : A`. For an inverse system `F : ℕᵒᵖ ⥤ A` we compare the `Ext`-groups
`Ext (Δ Z) F i` in the category of inverse systems (the right derived functors of
`F ↦ lim Hom(Z, Fₙ)`, e.g. continuous étale cohomology) with the inverse limit of the
levelwise `Ext`-groups `Ext Z Fₙ i`.

In general the two differ by a `lim¹`-term (Jannsen). We prove the comparison
isomorphism in degree `0` unconditionally, and in degree `i + 1` under the hypothesis
that the degree-`i` levelwise `Ext`-system satisfies the Mittag-Leffler condition
(`CategoryTheory.Functor.IsMittagLeffler`, which forces the relevant `lim¹` to
vanish); the latter holds in particular when the transition maps of that system are
surjective, or when its groups are finite:

- `CategoryTheory.Abelian.Ext.zeroAddEquivLimitLevelSystem`
- `CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem`
- `CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem_of_surjective`

The proof is by dimension shifting along `0 → F → I → Q → 0` with `I` injective: the
degree-one case is an explicit Mittag-Leffler eventual-image argument for the
four-term exact sequences of systems
`0 → Hom(Z,F•) → Hom(Z,I•) → Hom(Z,Q•) → Ext¹(Z,F•) → 0`
(using that the transition maps of `Hom(Z,I•)` are split surjections), and the
inductive step uses the connecting isomorphisms on both sides, with naturality in the
system direction provided by `ShortComplex.ShortExact.extClass_naturality`.
-/

universe w t v u

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Abelian
namespace Ext

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]


section Main

variable [EnoughInjectives A] [HasProductsOfShape ℕ A]

variable (Z : A)


variable {SC : ShortComplex (ℕᵒᵖ ⥤ A)}


omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Levelwise exactness at the third object: classes killed by the connecting map come
from the middle object. -/
lemma exists_of_levelDelta_app_eq_zero
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (c : Ext Z (SC.X₃.obj k) i)
    (hc : ConcreteCategory.hom ((levelDelta Z hSCk i).app k) c = 0) :
    ∃ b : Ext Z (SC.X₂.obj k) i,
      ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) b =
        c := by
  obtain ⟨b, hb⟩ := covariant_sequence_exact₃ Z (hSCk k) c rfl
    ((levelDelta_app_apply Z hSCk i k c).symm.trans hc)
  exact ⟨b, (whiskerRight_extFunctorObj_app_apply Z i k b).trans hb⟩


end Main

end Ext
end Abelian
end CategoryTheory


theorem solution.{sol_u1, sol_u2, sol_u3} : type_of% @CategoryTheory.Abelian.Ext.exists_of_levelDelta_app_eq_zero.{sol_u1, sol_u2, sol_u3} := @CategoryTheory.Abelian.Ext.exists_of_levelDelta_app_eq_zero.{sol_u1, sol_u2, sol_u3}
