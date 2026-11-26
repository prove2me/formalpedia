-- Prove2me | solution 1 for CategoryTheory.Sheaf.exists_mem_ext_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:21.658799+00:00
-- url     : https://prove2.me/submissions/f0d9ffe1-189b-4150-bda5-3396c11854c5

import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_LocallyVanish

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Positive degree Ext classes from free abelian sheaves vanish locally

Let `(C, J)` be a site and `F` a sheaf of abelian groups on it. We show that any class
`ξ : Ext (ℤ[U]) F (p + 1)`, where `ℤ[U]` is the free abelian sheaf on `U : C`, vanishes
locally: there exists a covering sieve `R` of `U` such that for every `g : W ⟶ U` in `R`,
the restriction of `ξ` along `g` is zero.

The proof is by induction on `p`, generalizing over `F`. Embedding `F` into an injective
sheaf `I` with quotient `Q`, the long exact sequence for `Ext (ℤ[U]) -` shows that `ξ` is
the product of a class `η : Ext (ℤ[U]) Q p` with the extension class of
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0`. For `p = 0`, the class `η` is a section of `Q` over `U`, which
locally lifts to `I` since `I ⟶ Q` is an epimorphism of sheaves, hence locally surjective;
restrictions of `ξ` then factor through the zero composite `(ℤ[W] ⟶ I ⟶ Q) ⋅ extClass`.
For `p > 0` the claim follows directly from the inductive hypothesis applied to `η`.
-/

universe w u

open CategoryTheory Limits Opposite

namespace CategoryTheory


open Abelian

variable {C : Type (u + 1)} [Category.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]


variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- Any positive degree `Ext`-class from the free abelian sheaf on `U : C` to a sheaf of
abelian groups `F` vanishes locally on `U`: its restrictions along all maps in a suitable
covering sieve of `U` are zero. -/
theorem Sheaf.exists_mem_ext_map_eq_zero (F : Sheaf J AddCommGrpCat.{u + 1}) (p : ℕ) {U : C}
    (ξ : Ext ((freeAbelianSheafFunctor J).obj U) F (p + 1)) :
    ∃ R ∈ J U, ∀ ⦃W : C⦄ (g : W ⟶ U), R.arrows g →
      (Ext.mk₀ ((freeAbelianSheafFunctor J).map g)).comp ξ (zero_add (p + 1)) = 0 := by
  induction p generalizing F with
  | zero =>
    -- Embed `F` into an injective object `I` with quotient `Q`.
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    -- `ξ` is the product of a degree zero class with the extension class of `S`.
    obtain ⟨η, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS ξ (Ext.eq_zero_of_injective _) rfl
    obtain ⟨s, rfl⟩ : ∃ s', Ext.mk₀ s' = η := ⟨_, Ext.mk₀_homEquiv₀_apply η⟩
    -- The epimorphism `I ⟶ Q` of sheaves is locally surjective.
    have : Presheaf.IsLocallySurjective J S.g.hom :=
      (Sheaf.isLocallySurjective_iff_epi' _ S.g).2 hS.epi_g
    refine ⟨Presheaf.imageSieve S.g.hom (freeAbelianSheafHomEquiv s),
      this.imageSieve_mem (freeAbelianSheafHomEquiv s), ?_⟩
    intro W g hg
    -- The restriction of the section `s` lifts to `I`, so it factors through `S.g`.
    have key : (freeAbelianSheafFunctor J).map g ≫ s =
        freeAbelianSheafHomEquiv.symm
          (Presheaf.localPreimage S.g.hom (freeAbelianSheafHomEquiv s) g hg) ≫ S.g := by
      apply freeAbelianSheafHomEquiv.injective
      rw [freeAbelianSheafHomEquiv_naturality_left, freeAbelianSheafHomEquiv_naturality_right,
        Equiv.apply_symm_apply]
      exact (Presheaf.app_localPreimage S.g.hom _ g hg).symm
    rw [Ext.mk₀_comp_comp, Ext.mk₀_comp_mk₀, key, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ p ih =>
    -- Embed `F` into an injective object `I` with quotient `Q` and write `ξ` as the
    -- product of a class of one degree lower with the extension class.
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨η, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS ξ (Ext.eq_zero_of_injective _) rfl
    obtain ⟨R, hR, H⟩ := ih S.X₃ η
    refine ⟨R, hR, ?_⟩
    intro W g hg
    rw [Ext.mk₀_comp_comp, H g hg, Ext.zero_comp]

end CategoryTheory


theorem solution.{sol_u1, sol_u2} : type_of% @CategoryTheory.Sheaf.exists_mem_ext_map_eq_zero.{sol_u1, sol_u2} := @CategoryTheory.Sheaf.exists_mem_ext_map_eq_zero.{sol_u1, sol_u2}
