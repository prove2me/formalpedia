-- Prove2me | solution 1 for CubicTurning.sharp_finite_balanced_law_lower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:47:18.58339+00:00
-- url     : https://prove2.me/submissions/396f6303-27ba-4949-ba33-a67827b2b8e2

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_balanced_central_mass
import Theorems.Thm_CubicTurning_central_history_forces_energy
import Theorems.Thm_CubicTurning_central_history_forces_energy_negative
import Theorems.Thm_CubicTurning_chain_start_middle
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning









theorem pairEnergy_nonneg (d₀ d₁ : ℂ) : 0 ≤ pairEnergy d₀ d₁ := by
  have h := Complex.re_le_norm (d₀ * conj d₁)
  rw [norm_mul, Complex.norm_conj] at h
  dsimp [pairEnergy]
  linarith




































































































end CubicTurning


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning












theorem sharp_family_center (t : ℝ) :
    sharpCentral t+sharpOuterPlus t+sharpOuterMinus t=0 := by
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus] <;> ring

theorem sharp_family_second (t : ℝ) :
    (sharpCentral t)^2+(sharpOuterPlus t)^2+(sharpOuterMinus t)^2=6 := by
  have hs : (Real.sqrt (3+3*t^2/4))^2=3+3*t^2/4 := Real.sq_sqrt (by positivity)
  simp only [pow_two] at hs
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus,pow_two,
    Complex.mul_re,Complex.mul_im] <;> nlinarith [hs]



theorem energy_nonneg (e d₀ d₁ : ℂ) : 0≤energy e d₀ d₁ := by
  unfold energy
  split_ifs
  · exact pairEnergy_nonneg _ _
  · rfl

theorem sharp_history_endpoint_energy (t : ℝ) (ht : 0<t) (ht1 : t≤1)
    (z : Fin 3 → ℂ) (e : ℂ)
    (hz : DerivativeChainPrivate.IsChain ![sharpCentral t,sharpOuterPlus t,sharpOuterMinus t] z)
    (hf : IsForward e (z 1-z 0) (z 2-z 1)) (hend : z 2=sharpCentral t) :
    energy e (z 1-z 0) (z 2-z 1)=2+2*Real.sqrt (1+t^2) := by
  obtain ⟨hz₀,hz₁⟩ := chain_start_middle _ _ _ (sharp_family_center t) (sharp_family_second t) z hz
  rcases hz₁ with hz₁|hz₁
  · rw [hz₀,hz₁,hend] at hf ⊢
    have hd : sharpCentral t-1=-1+Complex.I*(t:ℂ) := by unfold sharpCentral; ring
    rw [hd] at hf ⊢
    simpa using central_history_forces_energy t e ht ht1 (by simpa only [sub_zero] using hf)
  · rw [hz₀,hz₁,hend] at hf ⊢
    have hd : sharpCentral t-(-1)=1+Complex.I*(t:ℂ) := by unfold sharpCentral; ring
    rw [hd] at hf ⊢
    simpa using central_history_forces_energy_negative t e ht ht1 (by simpa only [sub_zero] using hf)












































end CubicTurning

open CubicTurning in
theorem solution {n : ℕ} (t : ℝ) (ht : 0<t) (ht1 : t≤1)
    (L : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)) :
    (2+2*Real.sqrt (1+t^2))/3≤L.meanEnergy := by
  have hi (i : Fin n) : (2+2*Real.sqrt (1+t^2))*
      (if L.paths i 2=sharpCentral t then L.weights i else 0) ≤
      L.weights i*energy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by
    by_cases hend : L.paths i 2=sharpCentral t
    · rw [if_pos hend,sharp_history_endpoint_energy t ht ht1 (L.paths i) (L.axes i) (L.actual i) (L.forward i) hend]
      ring_nf
      rfl
    · rw [if_neg hend,mul_zero]
      exact mul_nonneg (L.nonneg i) (energy_nonneg _ _ _)
  have hh:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  rw [←Finset.mul_sum,balanced_central_mass t ht L] at hh
  change _≤L.meanEnergy at hh
  linarith
