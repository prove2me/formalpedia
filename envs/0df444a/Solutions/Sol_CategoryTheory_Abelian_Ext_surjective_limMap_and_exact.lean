-- Prove2me | solution 1 for CategoryTheory.Abelian.Ext.surjective_limMap_and_exact
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:05.335661+00:00
-- url     : https://prove2.me/submissions/ca8ecad3-682c-4b93-b15c-aacdfad257b8

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


section AbChase

/-! ### Two Mittag-Leffler-type diagram chases for systems of abelian groups -/

variable {B C D : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (g : B ⟶ C) (h : C ⟶ D)

/-- A family of elements of an `ℕᵒᵖ`-indexed system of abelian groups which is
compatible with the successive transition maps assembles into an element of the limit
with the given components. -/
private lemma exists_limit_elem {F : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}
    (x : ∀ n : ℕ, ToType (F.obj (op n)))
    (hx : ∀ n, ConcreteCategory.hom (SequentialSystem.transition F n) (x (n + 1)) = x n) :
    ∃ t : ToType ((limit F : AddCommGrpCat.{w})), ∀ k : ℕᵒᵖ,
      ConcreteCategory.hom (limit.π F k) t = x k.unop := by
  have hxall : ∀ (m n : ℕ) (hmn : m ≤ n),
      ConcreteCategory.hom (F.map (homOfLE hmn).op) (x n) = x m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
      have h1 : (homOfLE (le_refl m)).op = 𝟙 (op m) := rfl
      calc ConcreteCategory.hom (F.map (homOfLE (le_refl m)).op) (x m)
          = ConcreteCategory.hom (F.map (𝟙 (op m))) (x m) := by rw [h1]
        _ = ConcreteCategory.hom (𝟙 (F.obj (op m))) (x m) := by rw [F.map_id]
        _ = x m := ConcreteCategory.id_apply _
    | succ n hmn ih =>
      have hsplit : (homOfLE (le_trans hmn (Nat.le_succ n))).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op := rfl
      calc ConcreteCategory.hom (F.map (homOfLE (le_trans hmn (Nat.le_succ n))).op)
            (x (n + 1))
          = ConcreteCategory.hom
              (F.map ((homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op)) (x (n + 1)) := by
            rw [hsplit]
        _ = ConcreteCategory.hom
              (F.map (homOfLE (Nat.le_succ n)).op ≫ F.map (homOfLE hmn).op)
              (x (n + 1)) := by
            rw [Functor.map_comp]
        _ = ConcreteCategory.hom (F.map (homOfLE hmn).op)
              (ConcreteCategory.hom (SequentialSystem.transition F n) (x (n + 1))) :=
            ConcreteCategory.comp_apply _ _ _
        _ = ConcreteCategory.hom (F.map (homOfLE hmn).op) (x n) := by rw [hx n]
        _ = x m := ih
  have hLF : IsLimit ((CategoryTheory.forget AddCommGrpCat.{w}).mapCone
      (limit.cone F)) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{w}) (limit.isLimit F)
  have hmemsec : (fun k : ℕᵒᵖ ↦ x k.unop) ∈
      (F ⋙ CategoryTheory.forget AddCommGrpCat.{w}).sections := by
    intro k k' f
    exact hxall k'.unop k.unop (leOfHom f.unop)
  exact ⟨(Types.isLimitEquivSections hLF).symm ⟨fun k ↦ x k.unop, hmemsec⟩,
    fun k ↦ Types.isLimitEquivSections_symm_apply hLF _ k⟩

/-- The components of an element of the limit are compatible with the successive
transition maps. -/
private lemma transition_π_apply {F : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ToType ((limit F : AddCommGrpCat.{w}))) (n : ℕ) :
    ConcreteCategory.hom (SequentialSystem.transition F n)
      (ConcreteCategory.hom (limit.π F (op (n + 1))) t) =
      ConcreteCategory.hom (limit.π F (op n)) t :=
  (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (limit.w F (homOfLE (Nat.le_succ n)).op) t)

/-- To identify the image of an element under `limMap`, it suffices to identify all of
its components. -/
private lemma limMap_apply_eq {F G : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G)
    (s : ToType ((limit F : AddCommGrpCat.{w})))
    (t : ToType ((limit G : AddCommGrpCat.{w})))
    (hst : ∀ k : ℕᵒᵖ, ConcreteCategory.hom (τ.app k)
      (ConcreteCategory.hom (limit.π F k) s) = ConcreteCategory.hom (limit.π G k) t) :
    ConcreteCategory.hom (limMap τ) s = t := by
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  calc ConcreteCategory.hom (limit.π G k) (ConcreteCategory.hom (limMap τ) s)
      = ConcreteCategory.hom (limMap τ ≫ limit.π G k) s :=
        (ConcreteCategory.comp_apply _ _ _).symm
    _ = ConcreteCategory.hom (limit.π F k ≫ τ.app k) s :=
        ConcreteCategory.congr_hom (limMap_π τ k) s
    _ = ConcreteCategory.hom (τ.app k) (ConcreteCategory.hom (limit.π F k) s) :=
        ConcreteCategory.comp_apply _ _ _
    _ = ConcreteCategory.hom (limit.π G k) t := hst k

/-! #### The Mittag-Leffler condition for systems of abelian groups -/


/-- **Exchange of limit and cokernel under Mittag-Leffler hypotheses.** Suppose
`B ⟶ C ⟶ D` are maps of inverse systems of abelian groups which are levelwise exact at
`C`, `h` is levelwise surjective, the transition maps of `B` are surjective, and the
kernels of `g` satisfy the Mittag-Leffler condition (in the stabilized elementwise
form: for each `n` there is `m ≥ n` such that the image in level `n` of any element of
the kernel at level `m` is the image of a kernel element from every level `k ≥ n`).
Then `limMap h` induces an isomorphism from the cokernel of `limMap g`: every element
of `limit D` lifts to `limit C`, and elements of `limit C` killed by `limMap h` come
from `limit B`. -/
lemma surjective_limMap_and_exact
    (hcomp : ∀ (k : ℕᵒᵖ) (b : B.obj k), ConcreteCategory.hom (h.app k)
      (ConcreteCategory.hom (g.app k) b) = 0)
    (hexact : ∀ (k : ℕᵒᵖ) (c : C.obj k), ConcreteCategory.hom (h.app k) c = 0 →
      ∃ b : B.obj k, ConcreteCategory.hom (g.app k) b = c)
    (hsurj : ∀ k, Function.Surjective (ConcreteCategory.hom (h.app k)))
    (hB : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition B n)))
    (hker : ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
      ∀ b : B.obj (op m), ConcreteCategory.hom (g.app (op m)) b = 0 →
        ∃ b' : B.obj (op k), ConcreteCategory.hom (g.app (op k)) b' = 0 ∧
          ConcreteCategory.hom (B.map (homOfLE hk).op) b' =
            ConcreteCategory.hom (B.map (homOfLE hm).op) b) :
    Function.Surjective (ConcreteCategory.hom (limMap h)) ∧
      ∀ c : (limit C : AddCommGrpCat.{w}), ConcreteCategory.hom (limMap h) c = 0 →
        ∃ b : (limit B : AddCommGrpCat.{w}), ConcreteCategory.hom (limMap g) b = c := by
  constructor
  · -- Surjectivity of `limMap h`, by a Mittag-Leffler correction recursion.
    intro t
    let y : ∀ n : ℕ, ToType (D.obj (op n)) :=
      fun n ↦ ConcreteCategory.hom (limit.π D (op n)) t
    have step : ∀ (n : ℕ) (cn : ToType (C.obj (op n))),
        ConcreteCategory.hom (h.app (op n)) cn = y n →
        ∃ cs : ToType (C.obj (op (n + 1))),
          ConcreteCategory.hom (h.app (op (n + 1))) cs = y (n + 1) ∧
          ConcreteCategory.hom (SequentialSystem.transition C n) cs = cn := by
      intro n cn hcn
      obtain ⟨z, hz⟩ := hsurj (op (n + 1)) (y (n + 1))
      have hnatz : ConcreteCategory.hom (h.app (op n))
          (ConcreteCategory.hom (SequentialSystem.transition C n) z) = y n := by
        calc ConcreteCategory.hom (h.app (op n))
              (ConcreteCategory.hom (SequentialSystem.transition C n) z)
            = ConcreteCategory.hom (SequentialSystem.transition C n ≫ h.app (op n))
                z :=
              (ConcreteCategory.comp_apply _ _ _).symm
          _ = ConcreteCategory.hom
                (h.app (op (n + 1)) ≫ SequentialSystem.transition D n) z :=
              ConcreteCategory.congr_hom (h.naturality (homOfLE (Nat.le_succ n)).op) z
          _ = ConcreteCategory.hom (SequentialSystem.transition D n)
                (ConcreteCategory.hom (h.app (op (n + 1))) z) :=
              ConcreteCategory.comp_apply _ _ _
          _ = ConcreteCategory.hom (SequentialSystem.transition D n) (y (n + 1)) := by
              rw [hz]
          _ = y n := transition_π_apply t n
      have h0 : ConcreteCategory.hom (h.app (op n))
          (cn - ConcreteCategory.hom (SequentialSystem.transition C n) z) = 0 := by
        rw [map_sub, hcn, hnatz, sub_self]
      obtain ⟨b, hb⟩ := hexact (op n) _ h0
      obtain ⟨b', hb'⟩ := hB n b
      have hgb' : ConcreteCategory.hom (SequentialSystem.transition C n)
          (ConcreteCategory.hom (g.app (op (n + 1))) b') =
          cn - ConcreteCategory.hom (SequentialSystem.transition C n) z := by
        calc ConcreteCategory.hom (SequentialSystem.transition C n)
              (ConcreteCategory.hom (g.app (op (n + 1))) b')
            = ConcreteCategory.hom
                (g.app (op (n + 1)) ≫ SequentialSystem.transition C n) b' :=
              (ConcreteCategory.comp_apply _ _ _).symm
          _ = ConcreteCategory.hom (SequentialSystem.transition B n ≫ g.app (op n))
                b' :=
              (ConcreteCategory.congr_hom (g.naturality (homOfLE (Nat.le_succ n)).op)
                b').symm
          _ = ConcreteCategory.hom (g.app (op n))
                (ConcreteCategory.hom (SequentialSystem.transition B n) b') :=
              ConcreteCategory.comp_apply _ _ _
          _ = ConcreteCategory.hom (g.app (op n)) b := by rw [hb']
          _ = cn - ConcreteCategory.hom (SequentialSystem.transition C n) z := hb
      refine ⟨z + ConcreteCategory.hom (g.app (op (n + 1))) b', ?_, ?_⟩
      · rw [map_add, hz, hcomp, add_zero]
      · rw [map_add, hgb']
        abel
    obtain ⟨c0, hc0⟩ := hsurj (op 0) (y 0)
    let c : ∀ n, {v : ToType (C.obj (op n)) //
        ConcreteCategory.hom (h.app (op n)) v = y n} :=
      fun n ↦ Nat.rec ⟨c0, hc0⟩
        (fun m ih ↦ ⟨(step m ih.1 ih.2).choose, (step m ih.1 ih.2).choose_spec.1⟩) n
    have hcc : ∀ n, ConcreteCategory.hom (SequentialSystem.transition C n)
        (c (n + 1)).1 = (c n).1 := fun n ↦ (step n (c n).1 (c n).2).choose_spec.2
    obtain ⟨s, hs⟩ := exists_limit_elem (fun n ↦ (c n).1) hcc
    refine ⟨s, limMap_apply_eq h s t fun k ↦ ?_⟩
    calc ConcreteCategory.hom (h.app k) (ConcreteCategory.hom (limit.π C k) s)
        = ConcreteCategory.hom (h.app k) (c k.unop).1 := by rw [hs k]
      _ = ConcreteCategory.hom (limit.π D k) t := (c k.unop).2
  · -- Exactness: elements of `limit C` killed by `limMap h` come from `limit B`, by
    -- a Mittag-Leffler eventual-image argument.
    intro t ht
    have hc0 : ∀ n : ℕ, ConcreteCategory.hom (h.app (op n))
        (ConcreteCategory.hom (limit.π C (op n)) t) = 0 := by
      intro n
      calc ConcreteCategory.hom (h.app (op n))
            (ConcreteCategory.hom (limit.π C (op n)) t)
          = ConcreteCategory.hom (limit.π C (op n) ≫ h.app (op n)) t :=
            (ConcreteCategory.comp_apply _ _ _).symm
        _ = ConcreteCategory.hom (limMap h ≫ limit.π D (op n)) t :=
            (ConcreteCategory.congr_hom (limMap_π h (op n)) t).symm
        _ = ConcreteCategory.hom (limit.π D (op n))
              (ConcreteCategory.hom (limMap h) t) :=
            ConcreteCategory.comp_apply _ _ _
        _ = ConcreteCategory.hom (limit.π D (op n)) 0 := by rw [ht]
        _ = 0 := map_zero _
    -- the components of `t` are compatible under all transition maps
    have htcomp : ∀ (a b : ℕ) (hab : a ≤ b),
        ConcreteCategory.hom (C.map (homOfLE hab).op)
          (ConcreteCategory.hom (limit.π C (op b)) t) =
          ConcreteCategory.hom (limit.π C (op a)) t := fun a b hab ↦
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        (ConcreteCategory.congr_hom (limit.w C (homOfLE hab).op) t)
    -- every component of `t` admits a preimage at its own level
    have hfib : ∀ n : ℕ, ∃ b : ToType (B.obj (op n)),
        ConcreteCategory.hom (g.app (op n)) b =
          ConcreteCategory.hom (limit.π C (op n)) t :=
      fun n ↦ hexact (op n) _ (hc0 n)
    -- pushing a preimage of a component of `t` down a transition map yields a
    -- preimage of the corresponding component
    have hpush : ∀ (a b' : ℕ) (hab : a ≤ b') (c : ToType (B.obj (op b'))),
        ConcreteCategory.hom (g.app (op b')) c =
          ConcreteCategory.hom (limit.π C (op b')) t →
        ConcreteCategory.hom (g.app (op a))
          (ConcreteCategory.hom (B.map (homOfLE hab).op) c) =
          ConcreteCategory.hom (limit.π C (op a)) t := by
      intro a b' hab c hc
      calc ConcreteCategory.hom (g.app (op a))
            (ConcreteCategory.hom (B.map (homOfLE hab).op) c)
          = ConcreteCategory.hom (B.map (homOfLE hab).op ≫ g.app (op a)) c :=
            (ConcreteCategory.comp_apply _ _ _).symm
        _ = ConcreteCategory.hom (g.app (op b') ≫ C.map (homOfLE hab).op) c :=
            ConcreteCategory.congr_hom (g.naturality (homOfLE hab).op) c
        _ = ConcreteCategory.hom (C.map (homOfLE hab).op)
              (ConcreteCategory.hom (g.app (op b')) c) :=
            ConcreteCategory.comp_apply _ _ _
        _ = ConcreteCategory.hom (limit.π C (op a)) t := by
            rw [hc]; exact htcomp a b' hab
    -- pushing down in two stages agrees with pushing down at once
    have hfac : ∀ (a b' c' : ℕ) (h1 : a ≤ b') (h2 : b' ≤ c')
        (x : ToType (B.obj (op c'))),
        ConcreteCategory.hom (B.map (homOfLE (h1.trans h2)).op) x =
          ConcreteCategory.hom (B.map (homOfLE h1).op)
            (ConcreteCategory.hom (B.map (homOfLE h2).op) x) := by
      intro a b' c' h1 h2 x
      have hsplit : (homOfLE (h1.trans h2)).op =
          (homOfLE h2).op ≫ (homOfLE h1).op := rfl
      calc ConcreteCategory.hom (B.map (homOfLE (h1.trans h2)).op) x
          = ConcreteCategory.hom (B.map ((homOfLE h2).op ≫ (homOfLE h1).op)) x := by
            rw [hsplit]
        _ = ConcreteCategory.hom
              (B.map (homOfLE h2).op ≫ B.map (homOfLE h1).op) x := by
            rw [Functor.map_comp]
        _ = _ := ConcreteCategory.comp_apply _ _ _
    -- stabilization levels of the kernel system
    choose μ hμ hstab using hker
    -- the "eventual fiber" at level `n`: preimages of the component of `t` which come
    -- from a preimage at the stabilization level `μ n`
    set P : ∀ n : ℕ, ToType (B.obj (op n)) → Prop := fun n b ↦
      ∃ b₀ : ToType (B.obj (op (μ n))),
        ConcreteCategory.hom (g.app (op (μ n))) b₀ =
          ConcreteCategory.hom (limit.π C (op (μ n))) t ∧
        ConcreteCategory.hom (B.map (homOfLE (hμ n)).op) b₀ = b with hPdef
    -- elements of the eventual fiber are preimages of the components of `t`
    have hPfib : ∀ (n : ℕ) (b : ToType (B.obj (op n))), P n b →
        ConcreteCategory.hom (g.app (op n)) b =
          ConcreteCategory.hom (limit.π C (op n)) t := by
      rintro n b ⟨b₀, hb₀, rfl⟩
      exact hpush n (μ n) (hμ n) b₀ hb₀
    -- key step: an element of the eventual fiber at `n` is the image of an element of
    -- the fiber at any level `k ≥ μ n`
    have stepA : ∀ (n k : ℕ) (hk : μ n ≤ k) (b : ToType (B.obj (op n))), P n b →
        ∃ c : ToType (B.obj (op k)),
          ConcreteCategory.hom (g.app (op k)) c =
            ConcreteCategory.hom (limit.π C (op k)) t ∧
          ConcreteCategory.hom (B.map (homOfLE ((hμ n).trans hk)).op) c = b := by
      rintro n k hk b ⟨b₀, hb₀, rfl⟩
      obtain ⟨c₀, hc₀⟩ := hfib k
      -- the discrepancy at level `μ n` lies in the kernel of `g`
      have hdis : ConcreteCategory.hom (g.app (op (μ n)))
          (ConcreteCategory.hom (B.map (homOfLE hk).op) c₀ - b₀) = 0 := by
        rw [map_sub, hpush (μ n) k hk c₀ hc₀, hb₀, sub_self]
      obtain ⟨κ, hκ0, hκτ⟩ := hstab n k ((hμ n).trans hk) _ hdis
      refine ⟨c₀ - κ, ?_, ?_⟩
      · rw [map_sub, hκ0, sub_zero, hc₀]
      · rw [map_sub, hκτ, map_sub, ← hfac n (μ n) k (hμ n) hk c₀]
        abel
    -- the eventual fibers are nonempty and map onto each other under the transitions
    have stepB : ∀ (n : ℕ) (b : ToType (B.obj (op n))), P n b →
        ∃ b' : ToType (B.obj (op (n + 1))), P (n + 1) b' ∧
          ConcreteCategory.hom (SequentialSystem.transition B n) b' = b := by
      intro n b hb
      obtain ⟨c, hcfib, hcτ⟩ := stepA n (max (μ n) (μ (n + 1))) (le_max_left _ _) b hb
      have h1 : n + 1 ≤ max (μ n) (μ (n + 1)) := (hμ (n + 1)).trans (le_max_right _ _)
      refine ⟨ConcreteCategory.hom (B.map (homOfLE h1).op) c,
        ⟨ConcreteCategory.hom (B.map (homOfLE (le_max_right (μ n) (μ (n + 1)))).op) c,
          hpush (μ (n + 1)) _ (le_max_right _ _) c hcfib,
          (hfac (n + 1) (μ (n + 1)) _ (hμ (n + 1)) (le_max_right _ _) c).symm⟩, ?_⟩
      exact (hfac n (n + 1) _ (Nat.le_succ n) h1 c).symm.trans hcτ
    -- choose a compatible family of preimages through the eventual fibers
    obtain ⟨binit, hbinit⟩ := hfib (μ 0)
    have hP0 : P 0 (ConcreteCategory.hom (B.map (homOfLE (hμ 0)).op) binit) :=
      ⟨binit, hbinit, rfl⟩
    let b : ∀ n, {v : ToType (B.obj (op n)) // P n v} :=
      fun n ↦ Nat.rec ⟨_, hP0⟩
        (fun m ih ↦ ⟨(stepB m ih.1 ih.2).choose, (stepB m ih.1 ih.2).choose_spec.1⟩) n
    have hbc : ∀ n, ConcreteCategory.hom (SequentialSystem.transition B n)
        (b (n + 1)).1 = (b n).1 := fun n ↦ (stepB n (b n).1 (b n).2).choose_spec.2
    obtain ⟨s, hs⟩ := exists_limit_elem (fun n ↦ (b n).1) hbc
    refine ⟨s, limMap_apply_eq g s t fun k ↦ ?_⟩
    calc ConcreteCategory.hom (g.app k) (ConcreteCategory.hom (limit.π B k) s)
        = ConcreteCategory.hom (g.app k) (b k.unop).1 := by rw [hs k]
      _ = ConcreteCategory.hom (limit.π C k) t := hPfib k.unop _ (b k.unop).2

end AbChase


end Ext
end Abelian
end CategoryTheory


theorem solution.{sol_u1} : type_of% @CategoryTheory.Abelian.Ext.surjective_limMap_and_exact.{sol_u1} := @CategoryTheory.Abelian.Ext.surjective_limMap_and_exact.{sol_u1}
