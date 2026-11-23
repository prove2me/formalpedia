-- Prove2me | solution 1 for Formalism.L2.Th1.H.ThIsom_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:53.342827+00:00
-- url     : https://prove2.me/submissions/85aae0ab-1641-4a33-9456-3d0c45341bec

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : OpUIsom) : ThIsom := by
  intro V W _ _ _ _ _ _ H H' g hiso Λ α' G
  have hgA : ∀ v : V, AnalyticAt ℂ (fun v => g v) v := by
    intro v
    have := (LinearMap.toContinuousLinearMap (g : V →ₗ[ℂ] W)).analyticAt v
    exact this
  have hgsA : ∀ w : W, AnalyticAt ℂ (fun w => g.symm w) w := by
    intro w
    have := (LinearMap.toContinuousLinearMap (g.symm : W →ₗ[ℂ] V)).analyticAt w
    exact this
  constructor
  · intro hG
    have hG' : AnalyticOnNhd ℂ G Set.univ ∧
        G ∈ fixedBy H' α' (imgLat (g : V →ₗ[ℂ] W) Λ) := hG
    have hinv : ∀ x ∈ imgLat (g : V →ₗ[ℂ] W) Λ, ∀ z, α' x * opU H' x G z = G z :=
      hG'.2
    show AnalyticOnNhd ℂ (fun v => G (g v)) Set.univ ∧
      (fun v => G (g v)) ∈ fixedBy H (fun v => α' (g v)) Λ
    refine ⟨fun v _ => (hG'.1 (g v) (Set.mem_univ _)).comp (hgA v), ?_⟩
    show ∀ x ∈ Λ, ∀ z, α' (g x) * opU H x (fun v => G (g v)) z = G (g z)
    intro x hx z
    have e := h V W H H' (g : V →ₗ[ℂ] W) hiso x G z
    have m : (g : V →ₗ[ℂ] W) x ∈ imgLat (g : V →ₗ[ℂ] W) Λ :=
      AddSubgroup.mem_map_of_mem (g : V →ₗ[ℂ] W).toAddMonoidHom hx
    have h3 := hinv _ m (g z)
    exact (congrArg (fun t => α' (g x) * t) e).trans h3
  · intro hG
    have hG' : AnalyticOnNhd ℂ (fun v => G (g v)) Set.univ ∧
        (fun v => G (g v)) ∈ fixedBy H (fun v => α' (g v)) Λ := hG
    have hinv : ∀ x ∈ Λ, ∀ z, α' (g x) * opU H x (fun v => G (g v)) z = G (g z) :=
      hG'.2
    show AnalyticOnNhd ℂ G Set.univ ∧ G ∈ fixedBy H' α' (imgLat (g : V →ₗ[ℂ] W) Λ)
    refine ⟨fun w _ => ?_, ?_⟩
    · have h3 := (hG'.1 (g.symm w) (Set.mem_univ _)).comp (hgsA w)
      have e : ((fun v => G (g v)) ∘ fun w => g.symm w) = G := funext fun w => by simp
      rw [e] at h3
      exact h3
    · show ∀ x ∈ imgLat (g : V →ₗ[ℂ] W) Λ, ∀ z, α' x * opU H' x G z = G z
      intro x hx z
      have hx' : x ∈ Λ.map (g : V →ₗ[ℂ] W).toAddMonoidHom := hx
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx'
      have e := h V W H H' (g : V →ₗ[ℂ] W) hiso y G (g.symm z)
      have hz : (g : V →ₗ[ℂ] W) (g.symm z) = z := g.apply_symm_apply z
      rw [hz] at e
      have h3 := hinv y hy (g.symm z)
      have h4 : G (g (g.symm z)) = G z := by rw [g.apply_symm_apply]
      exact (congrArg (fun t => α' (g y) * t) e).symm.trans (h3.trans h4)
end Formalism.L2.Th1.H
