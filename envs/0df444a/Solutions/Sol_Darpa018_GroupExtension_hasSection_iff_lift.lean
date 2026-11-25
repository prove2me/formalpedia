-- Prove2me | solution 1 for Darpa018.GroupExtension.hasSection_iff_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:05.17424+00:00
-- url     : https://prove2.me/submissions/1b3451ee-f346-4e72-92d7-cbbf2c88e7ec

module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.NoncommRing
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Definitions.Def_DarpaH2Lifting_Solution

set_option autoImplicit false
@[expose] public section
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Darpa018 Darpa018.GroupExtension
open scoped IsMulCommutative
variable {G E Q : Type} [Group G] [Group E] [Group Q]
variable (q : E →* Q) [IsMulCommutative q.ker]
variable (ρ : G →* Q) (l : G → E) (hl : ∀ g, q (l g) = ρ g)
namespace Darpa018.GroupExtension
theorem _root_.solution :
    letI := kernelAction q ρ l hl
    H2Core.HasSection (defect q ρ l hl) ↔ ∃ f : G →* E, q.comp f = ρ := by
  let := kernelAction q ρ l hl
  constructor
  · rintro ⟨t, ht⟩
    let F : G → E := fun g => (t g).toMul * l g
    have hF (g h : G) : F (g * h) = F g * F h := by
      have heq := congrArg (fun z : Additive q.ker => (z.toMul : E)) (ht g h)
      change ((t (g * h)).toMul : E) =
        ((t g).toMul * (l g * (t h).toMul * (l g)⁻¹)) *
          (l g * l h * (l (g * h))⁻¹) at heq
      change ((t (g * h)).toMul : E) * l (g * h) =
        ((t g).toMul * l g) * ((t h).toMul * l h)
      rw [heq]
      group
    refine ⟨MonoidHom.mk' F hF, ?_⟩
    ext g
    change q ((t g).toMul * l g) = ρ g
    rw [map_mul, (t g).toMul.property, one_mul, hl]
  · rintro ⟨f, hf⟩
    have hfg (g : G) : q (f g) = ρ g := DFunLike.congr_fun hf g
    let t : G → Additive q.ker := fun g =>
      Additive.ofMul ⟨f g * (l g)⁻¹, by simp [MonoidHom.mem_ker, hfg, hl]⟩
    refine ⟨t, ?_⟩
    intro g h
    apply Additive.toMul.injective
    apply Subtype.ext
    change f (g * h) * (l (g * h))⁻¹ =
      (f g * (l g)⁻¹ * (l g * (f h * (l h)⁻¹) * (l g)⁻¹)) *
        (l g * l h * (l (g * h))⁻¹)
    rw [map_mul]
    group
end Darpa018.GroupExtension
