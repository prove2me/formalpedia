-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lifting_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:00.604726+00:00
-- url     : https://prove2.me/submissions/3e4297e1-7e78-404f-93ce-f45e3d22ce49

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_aniso_decomp
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_aniso_isCompl
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lifting_anisotropic
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LiftUnitary := by
  intro K V _ _ _ _ _ H r F F' Wt h hA hA' hL hh
  have han := lifting_anisotropic K V H r F F' Wt hA hA' hL
  have hc := aniso_isCompl H Wt han
  let g : V →ₗ[K] V := LinearMap.ofIsCompl hc (Wt.subtype ∘ₗ h) (perpL H Wt).subtype
  have hgW : ∀ w : Wt, g (w : V) = (h w : V) := fun w => by
    simp [g]
  have hgP : ∀ y : V, (∀ w ∈ Wt, H.B y w = 0) → g y = y := fun y hy => by
    have := LinearMap.ofIsCompl_apply_right hc (φ := Wt.subtype ∘ₗ h) (ψ := (perpL H Wt).subtype) ⟨y, hy⟩
    simpa [g] using this
  have hsplit : ∀ y : V, ∃ a : Wt, ∃ b : V, (∀ w ∈ Wt, H.B b w = 0) ∧ y = (a : V) + b := by
    intro y
    obtain ⟨w, ⟨hw, hw'⟩, -⟩ := aniso_decomp H Wt han y
    exact ⟨⟨w, hw⟩, y - w, hw', by simp⟩
  have hiso : ∀ x y : V, H.B (g x) (g y) = H.B x y := by
    intro x y
    obtain ⟨a, b, hb, rfl⟩ := hsplit x
    obtain ⟨c, d, hd, rfl⟩ := hsplit y
    have e1 : g ((a : V) + b) = (h a : V) + b := by rw [map_add, hgW, hgP b hb]
    have e2 : g ((c : V) + d) = (h c : V) + d := by rw [map_add, hgW, hgP d hd]
    rw [e1, e2]
    simp only [map_add, LinearMap.add_apply, hh, hb _ (h c).2, hb _ c.2,
      B_swap0 H (hd _ (h a).2), B_swap0 H (hd _ a.2)]
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply H.nondeg
    intro y
    rw [← hiso, hx]; simp
  refine ⟨g, ⟨⟨hiso, hgP⟩, ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩, hgW⟩, ?_⟩
  rintro g' ⟨⟨-, hP'⟩, -, hW'⟩
  ext y
  obtain ⟨a, b, hb, rfl⟩ := hsplit y
  rw [map_add, map_add, hgW, hW', hgP b hb, hP' b hb]
end Formalism.HermitianLatticeCounting.P
