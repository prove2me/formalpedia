-- Prove2me | solution 1 for ClausiusDuhem.internal_energy_inequality
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:51.877312+00:00
-- url     : https://prove2.me/submissions/bead3c19-dd39-4e9a-a7a1-e838d2eaca87

import Definitions.Def_ClausiusDuhem_thermo_process
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv

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

private theorem thermo_flux (T : Space → ℝ) (q : Space → Space) (x : Space)
    (hT : DifferentiableAt ℝ T x) (hq : DifferentiableAt ℝ q x) (hne : T x ≠ 0) :
    T x * div (fun y => (T y)⁻¹ • q y) x =
      div q x - dot (q x) (grad T x) / T x := by
  have hInv := (hasDerivAt_inv hne).hasFDerivAt.comp x hT.hasFDerivAt
  have hp (j : Fin 3) : partialDeriv (fun y => (T y)⁻¹) j x =
      -(T x ^ 2)⁻¹ * partialDeriv T j x := by
    unfold partialDeriv
    change (fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ T) x) (Pi.single j 1) = _
    rw [hInv.fderiv]
    simp [ContinuousLinearMap.comp_apply, smul_eq_mul, mul_comm]
  have hd := thermo_div_mul (fun y => (T y)⁻¹) q x hInv.differentiableAt hq
  have hg : dot (grad (fun y => (T y)⁻¹) x) (q x) =
      -(T x ^ 2)⁻¹ * dot (q x) (grad T x) := by
    simp only [dot, grad, hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hg] at hd
  rw [hd]
  field_simp [hne]
  ring

theorem solution (P : ThermoProcess) (hP : P.Smooth)
    (hT : ∀ t x, 0 < P.temp t x) (hEntropy : P.EntropyInequality)
    (hEnergy : P.EnergyBalance) :
    P.InternalEnergyInequality := by
  intro t x
  have ht := hT t x
  have hf := thermo_flux (P.temp t) (P.heatFlux t) x
    (space_diff P.temp hP.2.2.2.2.1 t x)
    (space_diff P.heatFlux hP.2.2.2.1 t x) ht.ne'
  have he := mul_le_mul_of_nonneg_left (hEntropy t x) ht.le
  have hs : P.temp t x * (P.rho t x * P.source t x / P.temp t x) =
      P.rho t x * P.source t x := by field_simp [ht.ne']
  rw [mul_add, mul_neg, hs, hf] at he
  have hb := hEnergy t x
  nlinarith only [he, hb]

#print axioms solution



