-- Prove2me | solution 1 for FiniteEnergyPlane.forall_eq_or_forall_ne_of_tubeGraphs
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T22:27:39.000025+00:00
-- url     : https://prove2.me/submissions/c2a6d95c-60d7-47b6-96bb-ba6d72b95d16

import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_symm_div_sub
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_of_div_sub
import Theorems.Thm_FiniteEnergyPlane_forall_eq_or_forall_ne_of_complexGraph



/-! Glue for B `forall_eq_or_forall_ne_of_tubeGraphs` (95e9b5b2) from the children in
`Scratch/BT_Stmts`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The graph of `v ∘ ψ⁻¹` is `Jbar`-complex when `z ↦ (ψ z, v z)` is `Jbar`-holomorphic. -/
lemma bt_complexGraph_of_hol (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hψ' : ContDiff ℝ ∞ ψ.symm) (hv : ContDiff ℝ ∞ v)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (x e : ℂ) :
    (Jbar (x, v (ψ.symm x)) (e, fderiv ℝ (fun y => v (ψ.symm y)) x e)).2 =
      fderiv ℝ (fun y => v (ψ.symm y)) x
        (Jbar (x, v (ψ.symm x)) (e, fderiv ℝ (fun y => v (ψ.symm y)) x e)).1 := by
  have dψ : ∀ y, DifferentiableAt ℝ ψ y := fun y => (hψ.differentiable (by simp)) y
  have dψ' : ∀ y, DifferentiableAt ℝ ψ.symm y := fun y => (hψ'.differentiable (by simp)) y
  have dv : ∀ y, DifferentiableAt ℝ v y := fun y => (hv.differentiable (by simp)) y
  set z := ψ.symm x with hz
  have hxz : ψ z = x := ψ.apply_symm_apply x
  -- chain rule for `v ∘ ψ⁻¹`
  have hg : fderiv ℝ (fun y => v (ψ.symm y)) x = (fderiv ℝ v z).comp (fderiv ℝ ψ.symm x) :=
    fderiv_comp x (dv _) (dψ' x)
  -- `Dψ(z) ∘ Dψ⁻¹(x) = id` and `Dψ⁻¹(x) ∘ Dψ(z) = id`
  have hinv1 : ∀ a, fderiv ℝ ψ z (fderiv ℝ ψ.symm x a) = a := by
    intro a
    have hc : fderiv ℝ (fun y => ψ (ψ.symm y)) x = (fderiv ℝ ψ z).comp (fderiv ℝ ψ.symm x) :=
      fderiv_comp x (dψ _) (dψ' x)
    have hid : (fun y => ψ (ψ.symm y)) = id := funext fun y => ψ.apply_symm_apply y
    rw [hid, fderiv_id] at hc
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L a) hc
    simpa using this.symm
  have hinv2 : ∀ a, fderiv ℝ ψ.symm x (fderiv ℝ ψ z a) = a := by
    intro a
    have hc : fderiv ℝ (fun y => ψ.symm (ψ y)) z = (fderiv ℝ ψ.symm (ψ z)).comp (fderiv ℝ ψ z) :=
      fderiv_comp z (dψ' _) (dψ z)
    have hid : (fun y => ψ.symm (ψ y)) = id := funext fun y => ψ.symm_apply_apply y
    rw [hid, fderiv_id, hxz] at hc
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L a) hc
    simpa using this.symm
  have hprod : fderiv ℝ (fun y : ℂ => (ψ y, v y)) z = (fderiv ℝ ψ z).prod (fderiv ℝ v z) :=
    DifferentiableAt.fderiv_prodMk (dψ z) (dv z)
  set e₀ := fderiv ℝ ψ.symm x e with he₀
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ × ℂ => L e₀) (hhol z)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, hprod, ContinuousLinearMap.prod_apply, hxz] at hh
  rw [hinv1 e] at hh
  have hge : fderiv ℝ (fun y => v (ψ.symm y)) x e = fderiv ℝ v z e₀ := by
    rw [hg]; rfl
  rw [hge, ← hh, hg]
  simp only [ContinuousLinearMap.comp_apply, hinv2]

theorem forall_eq_or_forall_ne_of_tubeGraphs_glue (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0)
    (ψ₁ ψ₂ : ℂ ≃ₜ ℂ) (v₁ v₂ : ℂ → ℂ) (κ₁ κ₂ : ℂ) (b₁ b₂ : ℝ)
    (hψ₁ : ContDiff ℝ ∞ ψ₁) (hψ₁' : ContDiff ℝ ∞ ψ₁.symm) (hv₁ : ContDiff ℝ ∞ v₁)
    (hψ₂ : ContDiff ℝ ∞ ψ₂) (hψ₂' : ContDiff ℝ ∞ ψ₂.symm) (hv₂ : ContDiff ℝ ∞ v₂)
    (hv₁ρ : ∀ z, v₁ z ∈ ball (0 : ℂ) ρ) (hv₂ρ : ∀ z, v₂ z ∈ ball (0 : ℂ) ρ)
    (hhol₁ : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ₁ x, v₁ x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ₁ z, v₁ z)).comp (fderiv ℝ (fun x : ℂ => (ψ₁ x, v₁ x)) z))
    (hhol₂ : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ₂ x, v₂ x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ₂ z, v₂ z)).comp (fderiv ℝ (fun x : ℂ => (ψ₂ x, v₂ x)) z))
    (hκ₁ : κ₁ ≠ 0) (hb₁ : 0 < b₁)
    (hψ₁as : ExpDecayCInfty (fun p : ℝ × ℝ => ψ₁ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ₁) b₁)
    (hv₁as : ExpDecayCInfty (fun p : ℝ × ℝ => v₁ (cylInf p.1 p.2)) (-δ))
    (hκ₂ : κ₂ ≠ 0) (hb₂ : 0 < b₂)
    (hψ₂as : ExpDecayCInfty (fun p : ℝ × ℝ => ψ₂ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ₂) b₂)
    (hv₂as : ExpDecayCInfty (fun p : ℝ × ℝ => v₂ (cylInf p.1 p.2)) (-δ)) :
    (∀ z, v₂ z = v₁ (ψ₁.symm (ψ₂ z))) ∨ ∀ z, v₂ z ≠ v₁ (ψ₁.symm (ψ₂ z)) := by
  have hgas : ExpDecayCInfty (fun p : ℝ × ℝ => v₁ (ψ₁.symm (cylInf p.1 p.2))) (-δ) :=
    expDecayCInfty_comp_of_div_sub ψ₁.symm κ₁⁻¹ (inv_ne_zero hκ₁) b₁ hb₁
      (expDecayCInfty_symm_div_sub ψ₁ hψ₁ hψ₁' κ₁ hκ₁ b₁ hb₁ hψ₁as) v₁ (-δ) hv₁as
  exact forall_eq_or_forall_ne_of_complexGraph ρ b hb Jbar Jinf Sinf hT δ hδ hwind
    (fun x => v₁ (ψ₁.symm x)) (hv₁.comp hψ₁') (fun x => hv₁ρ _)
    (bt_complexGraph_of_hol Jbar ψ₁ v₁ hψ₁ hψ₁' hv₁ hhol₁) hgas ψ₂ v₂ κ₂ b₂ hψ₂ hv₂ hv₂ρ hhol₂
    hκ₂ hb₂ hψ₂as hv₂as

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0)
    (ψ₁ ψ₂ : ℂ ≃ₜ ℂ) (v₁ v₂ : ℂ → ℂ) (κ₁ κ₂ : ℂ) (b₁ b₂ : ℝ)
    (hψ₁ : ContDiff ℝ ∞ ψ₁) (hψ₁' : ContDiff ℝ ∞ ψ₁.symm) (hv₁ : ContDiff ℝ ∞ v₁)
    (hψ₂ : ContDiff ℝ ∞ ψ₂) (hψ₂' : ContDiff ℝ ∞ ψ₂.symm) (hv₂ : ContDiff ℝ ∞ v₂)
    (hv₁ρ : ∀ z, v₁ z ∈ ball (0 : ℂ) ρ) (hv₂ρ : ∀ z, v₂ z ∈ ball (0 : ℂ) ρ)
    (hhol₁ : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ₁ x, v₁ x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ₁ z, v₁ z)).comp (fderiv ℝ (fun x : ℂ => (ψ₁ x, v₁ x)) z))
    (hhol₂ : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ₂ x, v₂ x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ₂ z, v₂ z)).comp (fderiv ℝ (fun x : ℂ => (ψ₂ x, v₂ x)) z))
    (hκ₁ : κ₁ ≠ 0) (hb₁ : 0 < b₁)
    (hψ₁as : ExpDecayCInfty (fun p : ℝ × ℝ => ψ₁ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ₁) b₁)
    (hv₁as : ExpDecayCInfty (fun p : ℝ × ℝ => v₁ (cylInf p.1 p.2)) (-δ))
    (hκ₂ : κ₂ ≠ 0) (hb₂ : 0 < b₂)
    (hψ₂as : ExpDecayCInfty (fun p : ℝ × ℝ => ψ₂ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ₂) b₂)
    (hv₂as : ExpDecayCInfty (fun p : ℝ × ℝ => v₂ (cylInf p.1 p.2)) (-δ)) :
    (∀ z, v₂ z = v₁ (ψ₁.symm (ψ₂ z))) ∨ ∀ z, v₂ z ≠ v₁ (ψ₁.symm (ψ₂ z)) :=
  forall_eq_or_forall_ne_of_tubeGraphs_glue ρ b hb Jbar Jinf Sinf hT δ hδ hwind ψ₁ ψ₂ v₁ v₂ κ₁ κ₂ b₁ b₂ hψ₁ hψ₁' hv₁ hψ₂ hψ₂' hv₂ hv₁ρ hv₂ρ hhol₁ hhol₂ hκ₁ hb₁ hψ₁as hv₁as hκ₂ hb₂ hψ₂as hv₂as
