-- Prove2me | solution 1 for CategoryTheory.Abelian.Ext.subsingleton_pi
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:01.552102+00:00
-- url     : https://prove2.me/submissions/3a06c497-a099-464a-8594-5472543a0bbe

import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Vanishing of `Ext` into products and dimension shifting

Let `C` be an abelian category with `HasExt`. We record elementary consequences of the
covariant long exact `Ext`-sequence:

- `CategoryTheory.Abelian.Ext.subsingleton_x₁_of_shortExact`: if `0 → X₁ → X₂ → X₃ → 0` is
  exact, `Hom(Z, X₂) → Hom(Z, X₃)` is surjective and the positive `Ext`-groups from `Z` to
  `X₂` and `X₃` vanish, then the positive `Ext`-groups from `Z` to `X₁` vanish.
- `CategoryTheory.Abelian.Ext.subsingleton_pi`: if products indexed by `ι` are exact
  (levelwise epimorphisms induce an epimorphism on products), then vanishing of the
  positive `Ext`-groups `Ext Z (G i)` implies vanishing of `Ext Z (∏ᶜ G)`.
  This is the product analogue of `CategoryTheory.subsingleton_ext_coproduct` and is proved
  by the same dimension shifting argument.
- `CategoryTheory.Abelian.Ext.connectingEquiv`: the connecting isomorphism
  `Ext Z X₃ (n+1) ≃+ Ext Z X₁ (n+2)` when the adjacent `Ext`-groups of `X₂` vanish.
- `CategoryTheory.Abelian.Ext.oneEquivOfHomEquiv`: a comparison of `Ext¹`-groups across two
  ambient abelian categories, given short exact sequences with vanishing `Ext¹` of the
  middle objects and compatible additive equivalences on `Hom`-level.
-/

universe w w' t v v' u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Ext

section ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (Z : C)


include hS in
/-- If `Hom(Z, S.X₂) → Hom(Z, S.X₃)` is surjective and `Ext Z S.X₂ 1` vanishes, then
`Ext Z S.X₁ 1` vanishes: the degree-zero connecting homomorphism is surjective with
full kernel. -/
private lemma subsingleton_x₁_one
    (hsurj : ∀ s : Z ⟶ S.X₃, ∃ t : Z ⟶ S.X₂, t ≫ S.g = s)
    (h₂ : Subsingleton (Ext Z S.X₂ 1)) :
    Subsingleton (Ext Z S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  obtain ⟨s, rfl⟩ := deltaZero_surjective hS Z h₂ ξ
  exact (deltaZero_apply_eq_zero_iff hS Z s).2 (hsurj s)


end ShortExact

section Pi

variable {ι : Type t} [HasProductsOfShape ι C] [EnoughInjectives C]

omit [HasExt.{w} C] in
private lemma pi_comp_zero (B : ι → C) :
    (Limits.Pi.map fun i ↦ Injective.ι (B i)) ≫
      (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (B i))) = 0 := by
  ext i
  simp

omit [HasExt.{w} C] in
/-- The product of the canonical short exact sequences
`0 ⟶ B i ⟶ Injective.under (B i) ⟶ cokernel (Injective.ι (B i)) ⟶ 0` is short exact,
provided that products of levelwise epimorphisms are epimorphisms: the product of the
monomorphisms is a monomorphism since products preserve limits, and exactness in the
middle holds since `Pi.map` of the inclusions is a kernel of `Pi.map` of the
projections (constructed componentwise). -/
private lemma pi_shortExact
    (hepi : ∀ (A B : ι → C) (φ : ∀ i, A i ⟶ B i), (∀ i, Epi (φ i)) → Epi (Limits.Pi.map φ))
    (B : ι → C) :
    (ShortComplex.mk _ _ (pi_comp_zero B)).ShortExact := by
  haveI : Epi (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (B i))) :=
    hepi _ _ _ fun i ↦ inferInstance
  refine { exact := ?_ }
  apply ShortComplex.exact_of_f_is_kernel
  refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk ↦ ?_
  have hki : ∀ i, (k ≫ Pi.π (fun j ↦ Injective.under (B j)) i) ≫
      cokernel.π (Injective.ι (B i)) = 0 := fun i ↦ by
    simpa using congrArg
      (fun u ↦ u ≫ Pi.π (fun j ↦ cokernel (Injective.ι (B j))) i) hk
  choose l hl using fun i ↦
    (ShortComplex.exact_cokernel (Injective.ι (B i))).lift' _ (hki i)
  refine ⟨Pi.lift l, ?_⟩
  ext i
  simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc]
  exact hl i

/-- Every morphism into the product of the cokernels lifts to the product of the chosen
injectives, provided that `Ext Z (B i) 1` vanishes for all `i`: lift componentwise via
the covariant long exact sequence. -/
private lemma exists_pi_lift (Z : C) (B : ι → C)
    (hB : ∀ i, Subsingleton (Ext Z (B i) 1))
    (s : Z ⟶ ∏ᶜ fun i ↦ cokernel (Injective.ι (B i))) :
    ∃ t : Z ⟶ ∏ᶜ fun i ↦ Injective.under (B i),
      t ≫ (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (B i))) = s := by
  have hlift : ∀ i, ∃ tᵢ : Z ⟶ Injective.under (B i),
      tᵢ ≫ cokernel.π (Injective.ι (B i)) =
        s ≫ Pi.π (fun j ↦ cokernel (Injective.ι (B j))) i := by
    intro i
    have hSi : (ShortComplex.mk (Injective.ι (B i)) (cokernel.π (Injective.ι (B i)))
        (cokernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_cokernel _ }
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hSi
      (Ext.mk₀ (s ≫ Pi.π (fun j ↦ cokernel (Injective.ι (B j))) i)) (zero_add 1)
      ((hB i).elim _ _)
    obtain ⟨tᵢ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
    rw [Ext.mk₀_comp_mk₀] at hx₂
    exact ⟨tᵢ, (Ext.mk₀_bijective _ _).1 hx₂⟩
  choose t ht using hlift
  refine ⟨Pi.lift t, ?_⟩
  ext i
  rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc]
  exact ht i

/-- Degree-one case of `CategoryTheory.Abelian.Ext.subsingleton_pi`. -/
private lemma subsingleton_ext_pi_one
    (hepi : ∀ (A B : ι → C) (φ : ∀ i, A i ⟶ B i), (∀ i, Epi (φ i)) → Epi (Limits.Pi.map φ))
    (Z : C) (B : ι → C) (hB : ∀ i, Subsingleton (Ext Z (B i) 1)) :
    Subsingleton (Ext Z (∏ᶜ B) 1) := by
  have hT := pi_shortExact hepi B
  haveI : Injective (∏ᶜ fun i ↦ Injective.under (B i)) := inferInstance
  exact subsingleton_x₁_one hT Z (fun s ↦ exists_pi_lift Z B hB s)
    (subsingleton_of_injective Z (∏ᶜ fun i ↦ Injective.under (B i)) 0)

/-- If levelwise epimorphisms of `ι`-indexed families induce epimorphisms on products,
then vanishing of the positive `Ext`-groups from `Z` to each member of a family `G`
implies vanishing of the positive `Ext`-groups from `Z` to `∏ᶜ G`.

This is the product analogue of `CategoryTheory.subsingleton_ext_coproduct`, proved by
dimension shifting: embed each `G i` into an injective `J i` with cokernel `Q i`; the
product `∏ᶜ J` is injective and `0 → ∏ᶜ G → ∏ᶜ J → ∏ᶜ Q → 0` is short exact by the
product-exactness hypothesis; in degree `1` lift morphisms `Z ⟶ ∏ᶜ Q` componentwise
(using `Ext.covariant_sequence_exact₃` levelwise and vanishing of `Ext Z (G i) 1`), and in
higher degrees use the connecting isomorphism and induction on the degree bound. -/
lemma subsingleton_pi
    (hepi : ∀ (A B : ι → C) (φ : ∀ i, A i ⟶ B i), (∀ i, Epi (φ i)) → Epi (Limits.Pi.map φ))
    (Z : C) (G : ι → C) (hG : ∀ i q, 0 < q → Subsingleton (Ext Z (G i) q)) :
    ∀ q, 0 < q → Subsingleton (Ext Z (∏ᶜ G) q) := by
  -- Structure the induction as in `CategoryTheory.subsingleton_ext_coproduct`
  -- (`Proetale/Topology/Comparison/CohomologyComparison.lean`): prove by induction on `n`
  -- the statement
  -- `∀ G, (∀ i q, 0 < q → q ≤ n → Subsingleton (Ext Z (G i) q)) →`
  -- `  ∀ q, 0 < q → q ≤ n → Subsingleton (Ext Z (∏ᶜ G) q)`,
  -- with the short exact sequences `Sᵢ = (G i ⟶ Injective.under (G i) ⟶ Qᵢ)` and their
  -- product. For the product short complex use:
  -- * mono: `Pi.map` of monomorphisms is a monomorphism (products preserve limits);
  -- * epi: the hypothesis `hepi`;
  -- * exactness: `Pi.map (ι ∘ Injective.ι)` is the kernel of `Pi.map (cokernel.π _)`
  --   since the product functor `Limits.piObjFunctor`/`lim` preserves kernels.
  -- The product of injectives is injective (instance in
  -- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`).
  suffices h : ∀ (n : ℕ) (B : ι → C),
      (∀ i q, 0 < q → q ≤ n + 1 → Subsingleton (Ext Z (B i) q)) →
      ∀ q, 0 < q → q ≤ n + 1 → Subsingleton (Ext Z (∏ᶜ B) q) by
    intro q hq
    exact h q G (fun i q' hq' _ ↦ hG i q' hq') q hq (Nat.le_succ q)
  intro n
  induction n with
  | zero =>
    intro B hB q hq hq'
    obtain rfl : q = 1 := le_antisymm hq' hq
    exact subsingleton_ext_pi_one hepi Z B fun i ↦ hB i 1 one_pos le_rfl
  | succ n IH =>
    intro B hB q hq hq'
    obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
    obtain rfl | hq0 := Nat.eq_zero_or_pos q
    · exact subsingleton_ext_pi_one hepi Z B fun i ↦ hB i 1 one_pos (by omega)
    · have hT := pi_shortExact hepi B
      -- The componentwise vanishing transfers to the cokernels with bound lowered by one.
      have hQ : ∀ (i : ι) (q' : ℕ), 0 < q' → q' ≤ n + 1 →
          Subsingleton (Ext Z (cokernel (Injective.ι (B i))) q') := by
        intro i q' hq'' hq'''
        have hSi : (ShortComplex.mk (Injective.ι (B i)) (cokernel.π (Injective.ι (B i)))
            (cokernel.condition _)).ShortExact :=
          { exact := ShortComplex.exact_cokernel _ }
        refine subsingleton_of_forall_eq 0 fun χ ↦ ?_
        obtain ⟨q', rfl⟩ : ∃ m, q' = m + 1 := ⟨q' - 1, (Nat.succ_pred_eq_of_pos hq'').symm⟩
        obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hSi χ rfl
          ((hB i (q' + 1 + 1) (by omega) (by omega)).elim _ _)
        rw [← hx₂, eq_zero_of_injective x₂, Ext.zero_comp]
      refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
      obtain ⟨η, hη⟩ := covariant_sequence_exact₁ Z hT ξ (eq_zero_of_injective _) rfl
      rw [← hη, (IH (fun i ↦ cokernel (Injective.ι (B i))) hQ q hq0 (by omega)).elim η 0,
        Ext.zero_comp]

end Pi


end Ext

end Abelian
end CategoryTheory


theorem solution.{sol_u1, sol_u2, sol_u3, sol_u4} : type_of% @CategoryTheory.Abelian.Ext.subsingleton_pi.{sol_u1, sol_u2, sol_u3, sol_u4} := @CategoryTheory.Abelian.Ext.subsingleton_pi.{sol_u1, sol_u2, sol_u3, sol_u4}
