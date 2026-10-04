-- Prove2me | solution 1 for Feynman1948.schroedinger_equation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T21:16:18.501985+00:00
-- url     : https://prove2.me/submissions/b61bbf2f-629d-4540-bed5-3beb0e6231b1

import Definitions.Def_Feynman1948_WaveEquation
import Theorems.Thm_Feynman1948_free_step_first_order
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

open Complex Filter Topology SchwartzMap MeasureTheory Feynman1948

theorem solution (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (V : ℝ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => (stepEvolution ħ m V ε ψ x - ψ x) / ε) (𝓝[>] 0)
      (𝓝 (-(I / ħ) * hamiltonian ħ m V ψ x)) := by
  let c : ℂ := -I * (V x : ℂ) / ħ
  let phase : ℝ → ℂ := fun ε => Complex.exp (c * ε)
  have hphase_deriv : HasDerivAt phase c 0 := by
    simpa [phase] using (((hasDerivAt_id (0 : ℂ)).const_mul c).cexp.comp_ofReal)
  have hphase : Tendsto phase (𝓝[>] 0) (𝓝 1) := by
    simpa [phase] using hphase_deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hphase_slope : Tendsto (fun ε : ℝ => (phase ε - 1) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 c) := by
    simpa [phase, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal,
      div_eq_mul_inv, mul_comm] using
      hphase_deriv.tendsto_slope_zero_right
  have hstep (ε : ℝ) : stepEvolution ħ m V ε ψ x =
      phase ε * stepEvolution ħ m (fun _ => 0) ε ψ x := by
    have haction (y : ℝ) : shortTimeAction m V ε x y =
        shortTimeAction m (fun _ => 0) ε x y - ε * V x := by
      simp [shortTimeAction]
    have hint (y : ℝ) : Complex.exp (I * (shortTimeAction m V ε x y : ℂ) / ħ) * ψ y =
        phase ε * (Complex.exp (I * (shortTimeAction m (fun _ => 0) ε x y : ℂ) / ħ) * ψ y) := by
      have hexp : I * (shortTimeAction m V ε x y : ℂ) / ħ =
          c * ε + I * (shortTimeAction m (fun _ => 0) ε x y : ℂ) / ħ := by
        rw [haction]
        push_cast
        dsimp [c]
        ring
      rw [hexp, Complex.exp_add]
      simp only [phase, mul_assoc]
    unfold stepEvolution
    simp_rw [hint]
    rw [integral_const_mul]
    ring
  have hfree := free_step_first_order ħ m hħ hm ψ x
  have ht := (hphase.mul hfree).add (hphase_slope.mul_const (ψ x))
  have hlimit : 1 * (I * ħ / (2 * m) * deriv (deriv ψ) x) + c * ψ x =
      -(I / ħ) * hamiltonian ħ m V ψ x := by
    dsimp [c, hamiltonian]
    have hħ0 : (ħ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hħ
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    field_simp [hħ0, hm0]
    ring
  rw [hlimit] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [hstep]
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  field_simp [hε0]
  ring
