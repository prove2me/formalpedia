-- Prove2me | solution 1 for ClausiusDuhem.entropy_inequality_of_local
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:55.193031+00:00
-- url     : https://prove2.me/submissions/ff749d68-6c96-44a3-8654-2f5374dd7965

import Definitions.Def_ClausiusDuhem_thermo_process
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
open ClausiusDuhem

private theorem space_diff {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (φ : ℝ → Space → β) (hφ : IsC1Field φ) (t : ℝ) (x : Space) :
    DifferentiableAt ℝ (φ t) x := by
  exact (hφ.differentiable_one (t, x)).comp x
    ((differentiableAt_const t).prodMk differentiableAt_id)

private theorem time_diff (φ : ℝ → Space → ℝ) (hφ : IsC1Field φ) (t : ℝ) (x : Space) :
    DifferentiableAt ℝ (fun τ => φ τ x) t := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × Space => φ p.1 p.2) (t, x) :=
    hφ.differentiable_one (t, x)
  have hg : DifferentiableAt ℝ (fun τ : ℝ => (τ, x)) t :=
    (differentiableAt_id : DifferentiableAt ℝ (fun τ : ℝ => τ) t).prodMk (differentiableAt_const x)
  exact hd.comp t hg

private theorem thermo_div_mul (f : Space → ℝ) (V : Space → Space) (x : Space)
    (hf : DifferentiableAt ℝ f x) (hV : DifferentiableAt ℝ V x) :
    div (fun y => f y • V y) x = dot (grad f x) (V x) + f x * div V x := by
  have hc (j : Fin 3) : DifferentiableAt ℝ (fun y => V y j) x :=
    (differentiableAt_pi.mp hV) j
  calc
    div (fun y => f y • V y) x =
        ∑ j : Fin 3, (f x * partialDeriv (fun y => V y j) j x + V x j * partialDeriv f j x) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [partialDeriv]
      rw [fderiv_fun_mul hf (hc j)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = _ := by
      simp only [Finset.sum_add_distrib, dot, grad, div, Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem grad_mul_dot (f g : Space → ℝ) (x V : Space)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dot (grad (fun y => f y * g y) x) V =
      g x * dot (grad f x) V + f x * dot (grad g x) V := by
  simp only [dot, grad, partialDeriv, fderiv_fun_mul hf hg,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem solution (P : ThermoProcess) (hP : P.Smooth)
    (hLocal : ∀ t x, timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t x ≥
      -div (fun y => (P.rho t y * P.eta t y) • P.vel t y) x
      - div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) x
      + P.rho t x * P.source t x / P.temp t x)
    (hMass : P.MassConservation) :
    P.EntropyInequality := by
  intro t x
  have hr := space_diff P.rho hP.1 t x
  have he := space_diff P.eta hP.2.1 t x
  have hv := space_diff P.vel hP.2.2.1 t x
  have ht : timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t x =
      timeDeriv P.rho t x * P.eta t x + P.rho t x * timeDeriv P.eta t x := by
    exact deriv_fun_mul (time_diff P.rho hP.1 t x) (time_diff P.eta hP.2.1 t x)
  have hd := thermo_div_mul (fun y => P.rho t y * P.eta t y) (P.vel t) x (hr.mul he) hv
  rw [grad_mul_dot _ _ _ _ hr he] at hd
  have hm := hMass t x
  unfold materialDeriv at hm ⊢
  have hmc := congrArg (fun r : ℝ => P.eta t x * r) hm
  have hl := hLocal t x
  rw [ht, hd] at hl
  nlinarith only [hmc, hl]

#print axioms solution


