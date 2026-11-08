-- Prove2me | solution 1 for BlockchainMarketPower.f_strictMonoOn_price
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:34:43.168394+00:00
-- url     : https://prove2.me/submissions/957dcaa6-341e-43ac-b52c-d85208077f07

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

open BlockchainMarketPower in
theorem solution (Ψ γ' : ℝ) (hγ₀ : 0 < γ') (hγ₁ : γ' < 1) (hΨ₀ : 0 < Ψ) (hΨ₁ : Ψ ≤ 1) :
    (∀ P : ℝ, HasDerivAt (fun P => f P Ψ γ') (Ψ / 2 * (1 - γ' / 2 * (1 - Ψ) * (P - Ψ))) P) ∧
      (∀ P ∈ Set.Icc Ψ 1, Ψ / 2 * (1 - γ' / 2) ≤ Ψ / 2 * (1 - γ' / 2 * (1 - Ψ) * (P - Ψ))) ∧
      0 < Ψ / 2 * (1 - γ' / 2) ∧
      StrictMonoOn (fun P => f P Ψ γ') (Set.Icc Ψ 1) := by
  have hd : ∀ P : ℝ, HasDerivAt (fun P => f P Ψ γ') (Ψ / 2 * (1 - γ' / 2 * (1 - Ψ) * (P - Ψ))) P := by
    intro P
    have e : (fun P => f P Ψ γ') = fun P =>
        1 / 2 * (P - Ψ) * Ψ - γ' / 8 * ((P - Ψ) * (P - Ψ)) * Ψ * (1 - Ψ) := by
      funext P; unfold f; ring
    rw [e]
    have h1 : HasDerivAt (fun P => P - Ψ) 1 P := (hasDerivAt_id P).sub_const Ψ
    have h2 := (h1.const_mul (1 / 2)).mul_const Ψ
    have h3 := (((h1.mul h1).const_mul (γ' / 8)).mul_const Ψ).mul_const (1 - Ψ)
    exact (h2.sub h3).congr_deriv (by ring)
  have hb : ∀ P ∈ Set.Icc Ψ 1, Ψ / 2 * (1 - γ' / 2) ≤ Ψ / 2 * (1 - γ' / 2 * (1 - Ψ) * (P - Ψ)) := by
    rintro P ⟨hP1, hP2⟩
    have hA : (1 - Ψ) * (P - Ψ) ≤ 1 := by nlinarith
    have hA0 : 0 ≤ (1 - Ψ) * (P - Ψ) := mul_nonneg (by linarith) (by linarith)
    have : γ' / 2 * (1 - Ψ) * (P - Ψ) ≤ γ' / 2 := by
      rw [mul_assoc]; nlinarith
    nlinarith
  have hpos : 0 < Ψ / 2 * (1 - γ' / 2) := by
    apply mul_pos (by linarith); linarith
  refine ⟨hd, hb, hpos, ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc Ψ 1)
  · exact fun x _ => (hd x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    exact lt_of_lt_of_le hpos (hb x ⟨hx.1.le, hx.2.le⟩)
