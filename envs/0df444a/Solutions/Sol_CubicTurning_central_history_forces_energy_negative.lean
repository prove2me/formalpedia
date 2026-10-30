-- Prove2me | solution 1 for CubicTurning.central_history_forces_energy_negative
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:34:40.100343+00:00
-- url     : https://prove2.me/submissions/4555dd42-d42d-4de4-b302-2c1fba0d2881

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_central_history_forces_energy
import Theorems.Thm_CubicTurning_energy_conj
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning























































theorem pairEnergy_unit_mul (u : ℂ) (hu : ‖u‖=1) (d₀ d₁ : ℂ) :
    pairEnergy (u*d₀) (u*d₁)=pairEnergy d₀ d₁ := by
  have huc : u*conj u=1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hu]
    norm_num
  unfold pairEnergy
  rw [norm_mul,norm_mul,hu,one_mul,one_mul]
  have he : u*d₀*conj (u*d₁)=(u*conj u)*(d₀*conj d₁) := by
    simp only [map_mul]
    ring
  rw [he,huc,one_mul]





theorem energy_unit_mul (u : ℂ) (hu : ‖u‖=1) (e d₀ d₁ : ℂ) :
    energy e (u*d₀) (u*d₁) = energy (e*u) d₀ d₁ := by
  have hp := pairEnergy_unit_mul u hu d₀ d₁
  simp only [energy,halfSlope,norm_mul,hu,one_mul,←mul_assoc,hp]
  rfl
















































end CubicTurning

open CubicTurning in
theorem solution (t : ℝ) (e : ℂ) (ht : 0<t) (ht1 : t≤1)
    (hf : IsForward e (-1:ℂ) (1+Complex.I*(t:ℂ))) :
    energy e (-1:ℂ) (1+Complex.I*(t:ℂ))=2+2*Real.sqrt (1+t^2) := by
  have hf' : IsForward (-conj e) (1:ℂ) (-1+Complex.I*(t:ℂ)) := by
    rcases hf with ⟨he,h₀,h₁⟩
    refine ⟨by simpa [Complex.norm_conj] using he,?_,?_⟩
    · simpa [Complex.mul_re,Complex.conj_re] using h₀
    · simpa [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im] using h₁
  have hE := energy_unit_mul (-1:ℂ) (by norm_num) (conj e) (1:ℂ) (-1+Complex.I*(t:ℂ))
  have hh : energy (conj e) (conj (-1:ℂ)) (conj (1+Complex.I*(t:ℂ)))=
      energy (-conj e) 1 (-1+Complex.I*(t:ℂ)) := by
    convert hE using 1 <;> simp <;> ring
  rw [←energy_conj e (-1:ℂ) (1+Complex.I*(t:ℂ)),hh]
  exact central_history_forces_energy t (-conj e) ht ht1 hf'
