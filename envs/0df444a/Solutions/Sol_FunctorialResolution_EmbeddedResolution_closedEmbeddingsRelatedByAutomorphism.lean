-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.closedEmbeddingsRelatedByAutomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:13.874771+00:00
-- url     : https://prove2.me/submissions/b67fdd55-7f09-491e-8daf-0ccce03a4659

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_ClosedEmbeddingsIntoAffineSpace
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := by
  simp
  rfl
private theorem appTop_add {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : Γ(Y, ⊤)) :
    f.appTop (a + b) = f.appTop a + f.appTop b :=
  map_add (CommRingCat.Hom.hom f.appTop) a b
private theorem appTop_sub {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : Γ(Y, ⊤)) :
    f.appTop (a - b) = f.appTop a - f.appTop b :=
  map_sub (CommRingCat.Hom.hom f.appTop) a b
private theorem appTop_id_apply {X : Scheme.{u}} (x : Γ(X, ⊤)) :
    (𝟙 X : X ⟶ X).appTop x = x := by
  simp
private theorem exists_iso_affineSpace_sum_comp_eq_of_coord {S : Scheme.{u}} (n m : ℕ)
    {Y : Scheme.{u}}
    (p : Y ⟶ S)
    (e₁ : Y ⟶ AffineSpace (ULift.{u} (Fin n)) S)
    (e₂ : Y ⟶ AffineSpace (ULift.{u} (Fin m)) S)
    (h₁ : e₁ ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = p)
    (h₂ : e₂ ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S) = p)
    (F : Fin m → Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤))
    (hF : ∀ b : Fin m, e₁.appTop (F b)
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
    (G : Fin n → Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤))
    (hG : ∀ a : Fin n, e₂.appTop (G a)
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (L R : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S)
    (hLover : L ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hRover : R ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hLinl : ∀ a : Fin n, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (hLinr : ∀ b : Fin m, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinl : ∀ a : Fin n, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinr : ∀ b : Fin m, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) :
    ∃ Φ : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ≅ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      Φ.hom ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧ L ≫ Φ.hom = R := by
  obtain ⟨pr₁, hpr₁, hpr₁c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ a : Fin n, q.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n)))
            = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun a : ULift.{u} (Fin n) =>
          AffineSpace.coord S (ULift.up (Sum.inl a.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun a => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨pr₂, hpr₂, hpr₂c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin m)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ b : Fin m, q.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))
            = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun b : ULift.{u} (Fin m) =>
          AffineSpace.coord S (ULift.up (Sum.inr b.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun b => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have mkHom : ∀ v : ULift.{u} (Fin n ⊕ Fin m) → Γ(AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, ⊤),
      ∃ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
            ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), w.appTop (AffineSpace.coord S i) = v i :=
    fun v => ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) v,
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨σ, hσ, hσc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₁.appTop (F b)) i.down)
  obtain ⟨σ', hσ', hσ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₁.appTop (F b)) i.down)
  obtain ⟨τ, hτ, hτc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  obtain ⟨τ', hτ', hτ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  have hσinl : ∀ a : Fin n,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσc _
  have hσinr : ∀ b : Fin m,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₁.appTop (F b) := fun b => hσc _
  have hσ'inl : ∀ a : Fin n,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσ'c _
  have hσ'inr : ∀ b : Fin m,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₁.appTop (F b) := fun b => hσ'c _
  have hτinl : ∀ a : Fin n,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₂.appTop (G a) := fun a => hτc _
  have hτinr : ∀ b : Fin m,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτc _
  have hτ'inl : ∀ a : Fin n,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₂.appTop (G a) := fun a => hτ'c _
  have hτ'inr : ∀ b : Fin m,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτ'c _
  have hfix₁ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ a : Fin n,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤),
        w.appTop (pr₁.appTop x) = pr₁.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₁ = pr₁ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₁, hw]
      · rintro ⟨a⟩
        rw [comp_appTop_apply, hpr₁c a, hwc a]
    rw [← comp_appTop_apply, hcomp]
  have hfix₂ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ b : Fin m,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤),
        w.appTop (pr₂.appTop x) = pr₂.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₂ = pr₂ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₂, hw]
      · rintro ⟨b⟩
        rw [comp_appTop_apply, hpr₂c b, hwc b]
    rw [← comp_appTop_apply, hcomp]
  have hσσ' : σ ≫ σ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ', hσ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσ'inl a, hσinl a, appTop_id_apply]
      · rw [comp_appTop_apply, hσ'inr b, appTop_sub, hσinr b,
          hfix₁ σ hσ hσinl (F b), appTop_id_apply]
        ring
  have hσ'σ : σ' ≫ σ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hσ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσinl a, hσ'inl a, appTop_id_apply]
      · rw [comp_appTop_apply, hσinr b, appTop_add, hσ'inr b,
          hfix₁ σ' hσ' hσ'inl (F b), appTop_id_apply]
        ring
  have hττ' : τ ≫ τ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ', hτ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτ'inl a, appTop_add, hτinl a,
          hfix₂ τ hτ hτinr (G a), appTop_id_apply]
        ring
      · rw [comp_appTop_apply, hτ'inr b, hτinr b, appTop_id_apply]
  have hτ'τ : τ' ≫ τ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hτ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτinl a, appTop_sub, hτ'inl a,
          hfix₂ τ' hτ' hτ'inr (G a), appTop_id_apply]
        ring
      · rw [comp_appTop_apply, hτinr b, hτ'inr b, appTop_id_apply]
  obtain ⟨D, hDover, hcoordEq⟩ :
      ∃ d : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        d ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), d.appTop (AffineSpace.coord S i)
            = Sum.elim
                (fun a : Fin n =>
                  e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
                (fun b : Fin m =>
                  e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) i.down :=
    ⟨AffineSpace.homOfVector p (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
        (fun a : Fin n => e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
        (fun b : Fin m => e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
        i.down),
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have hDinl : ∀ a : Fin n,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := fun a => hcoordEq _
  have hDinr : ∀ b : Fin m,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := fun b => hcoordEq _
  have hLpr₁ : L ≫ pr₁ = e₁ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₁, hLover, h₁]
    · rintro ⟨a⟩
      rw [comp_appTop_apply, hpr₁c a, hLinl a]
  have hLF : ∀ b : Fin m, L.appTop (pr₁.appTop (F b))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := by
    intro b
    rw [← comp_appTop_apply, hLpr₁, hF b]
  have hDpr₂ : D ≫ pr₂ = e₂ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₂, hDover, h₂]
    · rintro ⟨b⟩
      rw [comp_appTop_apply, hpr₂c b, hDinr b]
  have hcompG : ∀ a : Fin n, D.appTop (pr₂.appTop (G a))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := by
    intro a
    rw [← comp_appTop_apply, hDpr₂, hG a]
  have hA : L ≫ σ = D := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hLover, hDover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσinl a, hLinl a, hDinl a]
      · rw [comp_appTop_apply, hσinr b, appTop_add, hLinr b, hLF b, hDinr b, zero_add]
  have hB : D ≫ τ = R := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hDover, hRover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτinl a, appTop_sub, hDinl a, hcompG a, hRinl a, sub_self]
      · rw [comp_appTop_apply, hτinr b, hDinr b, hRinr b]
  refine ⟨⟨σ ≫ τ, τ' ≫ σ', ?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc τ τ' σ', hττ', Category.id_comp, hσσ']
  · rw [Category.assoc, ← Category.assoc σ' σ τ, hσ'σ, Category.id_comp, hτ'τ]
  · show (σ ≫ τ) ≫ _ = _
    rw [Category.assoc, hτ, hσ]
  · show L ≫ (σ ≫ τ) = R
    rw [← Category.assoc, hA, hB]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution : ClosedEmbeddingsRelatedByAutomorphism.{u} := by
  intro k hk Y hY p hp n m e₁ he₁ e₂ he₂ h₁ h₂
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin n))) := by
    unfold affineSpaceIndexedBy; infer_instance
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin m))) := by
    unfold affineSpaceIndexedBy; infer_instance
  choose F hF using fun b : Fin m =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₁).2
      (e₂.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up b : ULift.{u} (Fin m))))
  choose G hG using fun a : Fin n =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₂).2
      (e₁.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up a : ULift.{u} (Fin n))))
  exact exists_iso_affineSpace_sum_comp_eq_of_coord n m p e₁ e₂ h₁ h₂ F hF G hG
    (AffineSpace.homOfVector p (coordVectorInl n m e₁))
    (AffineSpace.homOfVector p (coordVectorInr n m e₂))
    (AffineSpace.homOfVector_over _ _) (AffineSpace.homOfVector_over _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)
end FunctorialResolution.EmbeddedResolution
