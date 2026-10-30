-- Prove2me | solution 1 for CubicTurning.energy_conj
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:32:55.649676+00:00
-- url     : https://prove2.me/submissions/73fd2152-17b6-4bea-a49e-18ce15bbbe64

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


open CubicTurning in
theorem solution (e d₀ d₁ : ℂ) :
    energy (conj e) (conj d₀) (conj d₁)=energy e d₀ d₁ := by
  have hq (d : ℂ) : halfSlope (conj e) (conj d) = -halfSlope e d := by
    simp [halfSlope,←map_mul,Complex.norm_conj,Complex.conj_re,Complex.conj_im,neg_div]
    ring
  have hp : pairEnergy (conj d₀) (conj d₁)=pairEnergy d₀ d₁ := by
    simp only [pairEnergy,Complex.norm_conj,Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hi : ((1/7≤-halfSlope e d₀ ∧ -halfSlope e d₁≤-(1/7)) ∨
      (1/7≤-halfSlope e d₁ ∧ -halfSlope e d₀≤-(1/7))) ↔
      ((1/7≤halfSlope e d₀ ∧ halfSlope e d₁≤-(1/7)) ∨
      (1/7≤halfSlope e d₁ ∧ halfSlope e d₀≤-(1/7))) := by
    constructor <;> intro h <;> rcases h with ⟨h₀,h₁⟩|⟨h₀,h₁⟩
    · exact Or.inr ⟨by linarith,by linarith⟩
    · exact Or.inl ⟨by linarith,by linarith⟩
    · exact Or.inr ⟨by linarith,by linarith⟩
    · exact Or.inl ⟨by linarith,by linarith⟩
  simp only [energy,hq,hp,hi]
