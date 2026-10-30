-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_core_alignment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:56:38.601195+00:00
-- url     : https://prove2.me/submissions/01e7d2b2-5ad0-436b-bc37-f039e34e07ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ContactTopology_equivariant_legendrian_isotopy_extension
import Theorems.Thm_ContactTopology_equivariant_legendrian_core_curve_isotopy
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set Function
open scoped ContDiff
namespace ContactTopology.LegendrianExtension
open BirkhoffGlobalSection Set Function
open scoped ContDiff

/-- The remaining classification input is an isotopy of curves; ambient
contact extension is proved rather than included in the input. -/
theorem core_alignment_of_legendrian_curve_isotopy
    (classification : ∀ F : EquivariantSphereContactomorphism,
      ∃ k : ℝ × Plane → Phase, ContDiff ℝ ∞ k ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere) ∧
        InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle) ∧
        (∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle,
          phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) ∧
        (∀ u ∈ unitCircle, k (0,u) = F.toFun ![u 0,u 1,0,0]) ∧
        (∀ u ∈ unitCircle, k (1,u) = ![u 0,u 1,0,0]))
    (F : EquivariantSphereContactomorphism) :
    ∃ A : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy A) ∧
      ∀ x : ℝ, A.toFun (F.toFun
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) =
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] := by
  obtain ⟨k,hk,hsphere,hinj,hreg,hleg,hodd,h0,h1⟩ := classification F
  obtain ⟨A,hAiso,hA⟩ := ContactTopology.equivariant_legendrian_isotopy_extension
    k hk hsphere hinj hreg hleg hodd
  refine ⟨A,hAiso,?_⟩
  intro x
  let u : Plane := ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x)]
  have hu : u ∈ unitCircle := by
    dsimp [u,unitCircle,planeNormSq]
    nlinarith [Real.sin_sq_add_cos_sq (2*Real.pi*x)]
  have hh := hA u hu
  rw [h0 u hu,h1 u hu] at hh
  exact hh

end ContactTopology.LegendrianExtension

theorem solution
    (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism) :
    ∃ A : BirkhoffGlobalSection.EquivariantSphereContactomorphism,
      Nonempty (BirkhoffGlobalSection.EquivariantSphereContactIsotopy A) ∧
      ∀ x : ℝ, A.toFun (F.toFun
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) =
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] := by
  exact ContactTopology.LegendrianExtension.core_alignment_of_legendrian_curve_isotopy
    ContactTopology.equivariant_legendrian_core_curve_isotopy F
