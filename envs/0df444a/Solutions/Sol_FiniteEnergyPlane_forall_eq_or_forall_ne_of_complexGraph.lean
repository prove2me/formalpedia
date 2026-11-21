-- Prove2me | solution 1 for FiniteEnergyPlane.forall_eq_or_forall_ne_of_complexGraph
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T22:31:02.398252+00:00
-- url     : https://prove2.me/submissions/55607ca2-4042-41dd-a143-e8a496ff1b17

import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_hasLoopEigenWind_of_comp_add
import Theorems.Thm_FiniteEnergyPlane_exists_halfCyl_solution_of_complexGraph
import Theorems.Thm_FiniteEnergyPlane_forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution
import Theorems.Thm_FiniteEnergyPlane_normalCoeff_of_isStdTubeStructure



/-! Glue for B3 `forall_eq_or_forall_ne_of_complexGraph` from B3E, B3W and Z (8a3578c8). -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem forall_eq_or_forall_ne_of_complexGraph_glue (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgρ : ∀ x, g x ∈ ball (0 : ℂ) ρ)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    (∀ z, v z = g (ψ z)) ∨ ∀ z, v z ≠ g (ψ z) := by
  have hρ : 0 < ρ := by
    have := hgρ 0
    rw [mem_ball_zero_iff] at this
    exact lt_of_le_of_lt (norm_nonneg _) this
  obtain ⟨-, -, hSinf', -, -⟩ := normalCoeff_of_isStdTubeStructure ρ b hρ hb Jbar Jinf Sinf hT
  obtain ⟨P, S, w, d, C, hPinj, hζ, hM, hS, hSper, hd, hSas, hw, hwz, hgr⟩ :=
    exists_halfCyl_solution_of_complexGraph ρ b hb Jbar Jinf Sinf hT δ hδ g hg hgρ hgJ hgas
      ψ v κ b' hψ hv hvρ hhol hκ hb' hψas hvas
  set c : ℝ := Complex.arg κ / (2 * π) with hc
  have hsym0 : CauchyRiemannIndex.IsSymLoop Sinf := hT.2.2.2.2.2.2.1
  have hsym : CauchyRiemannIndex.IsSymLoop (fun t => Sinf (t + c)) := by
    refine ⟨hsym0.1.comp (continuous_id.add continuous_const), fun t => ?_, fun t => hsym0.2.2 _⟩
    show Sinf (t + 1 + c) = Sinf (t + c)
    rw [add_right_comm]
    exact hsym0.2.1 _
  have hsm : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf (t + c) i j) := fun i j =>
    (hSinf' i j).comp (contDiff_id.add contDiff_const)
  have hwind' : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind (fun t => Sinf (t + c)) μ k → k ≤ 0 :=
    fun μ hμ k h => hwind μ hμ k (hasLoopEigenWind_of_comp_add Sinf c μ k h)
  rcases forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution (fun z => P z (v z - g (ψ z))) hζ hM
      S hS hSper _ hsym hsm d hd hSas w hw hwz C δ hgr hwind' with h | h
  · left
    intro z
    have h0 : P z (v z - g (ψ z)) = P z 0 := by rw [map_zero]; exact h z
    exact sub_eq_zero.1 (hPinj z h0)
  · right
    intro z heq
    apply h z
    simp only [heq, sub_self, map_zero]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgρ : ∀ x, g x ∈ ball (0 : ℂ) ρ)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    (∀ z, v z = g (ψ z)) ∨ ∀ z, v z ≠ g (ψ z) :=
  forall_eq_or_forall_ne_of_complexGraph_glue ρ b hb Jbar Jinf Sinf hT δ hδ hwind g hg hgρ hgJ hgas ψ v κ b' hψ hv hvρ hhol hκ hb' hψas hvas
