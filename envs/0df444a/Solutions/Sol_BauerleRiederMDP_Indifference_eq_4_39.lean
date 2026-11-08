-- Prove2me | solution 1 for BauerleRiederMDP.Indifference.eq_4_39
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:38:01.967056+00:00
-- url     : https://prove2.me/submissions/3a0b645f-2c0f-4ea4-8b52-46ff01b5fcb1

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_v

open MeasureTheory

namespace Aux_BR_eq_4_39
open BauerleRiederMDP.Indifference

theorem key (A B α β : ℝ) (hA : 0 < A) (hB : 0 < B) (hα : 0 < α) (hβ : 0 < β) (a : ℝ) :
    A * Real.exp (-α * (Real.log (α * A / (β * B)) / (α + β))) +
        B * Real.exp (β * (Real.log (α * A / (β * B)) / (α + β))) ≤
      A * Real.exp (-α * a) + B * Real.exp (β * a) := by
  set a0 := Real.log (α * A / (β * B)) / (α + β) with ha0
  have hpos : 0 < α * A / (β * B) := by positivity
  have hfoc : β * B * Real.exp (β * a0) = α * A * Real.exp (-α * a0) := by
    have h1 : Real.exp ((α + β) * a0) = α * A / (β * B) := by
      rw [ha0, mul_div_cancel₀ _ (by positivity : (α + β) ≠ 0), Real.exp_log hpos]
    have h2 : Real.exp (β * a0) = Real.exp ((α + β) * a0) * Real.exp (-α * a0) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2, h1]; field_simp
  set h := a - a0
  have e1 : Real.exp (-α * a) = Real.exp (-α * a0) * Real.exp (-α * h) := by
    rw [← Real.exp_add]; congr 1; simp only [h]; ring
  have e2 : Real.exp (β * a) = Real.exp (β * a0) * Real.exp (β * h) := by
    rw [← Real.exp_add]; congr 1; simp only [h]; ring
  have f1 : -α * h + 1 ≤ Real.exp (-α * h) := Real.add_one_le_exp _
  have f2 : β * h + 1 ≤ Real.exp (β * h) := Real.add_one_le_exp _
  have p1 : 0 ≤ A * Real.exp (-α * a0) := by positivity
  have p2 : 0 ≤ B * Real.exp (β * a0) := by positivity
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left f1 p1
  have := mul_le_mul_of_nonneg_left f2 p2
  have h3 : h * (β * B * Real.exp (β * a0)) = h * (α * A * Real.exp (-α * a0)) := by rw [hfoc]
  nlinarith [h3]

theorem integral_eq (M : Market) (a : ℝ) :
    ∫ ω, Real.exp (-M.γ * a * (M.Rt ω - 1)) ∂M.P =
      (M.p 0 + M.p 1) * Real.exp (-(M.γ * (M.u - 1)) * a) +
        (M.p 2 + M.p 3) * Real.exp ((M.γ * (1 - M.d)) * a) := by
  rw [integral_fintype Integrable.of_finite]
  have hP : ∀ x, M.P.real {x} = M.p x := by
    intro x
    simp [Measure.real, Market.P, Measure.finsetSum_apply, Pi.single_apply, (M.p_pos x).le]
  have hR : M.Rt 0 = M.u ∧ M.Rt 1 = M.u ∧ M.Rt 2 = M.d ∧ M.Rt 3 = M.d := ⟨rfl, rfl, rfl, rfl⟩
  simp only [hP, Fin.sum_univ_four, smul_eq_mul]
  rw [hR.1, hR.2.1, hR.2.2.1, hR.2.2.2]
  rw [show -M.γ * a * (M.u - 1) = -(M.γ * (M.u - 1)) * a by ring,
    show -M.γ * a * (M.d - 1) = (M.γ * (1 - M.d)) * a by ring]
  ring

end Aux_BR_eq_4_39

open BauerleRiederMDP.Indifference Aux_BR_eq_4_39 in
theorem solution (M : Market) :
    (∃ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rt ω - 1)) ∂M.P = M.v) ∧ 0 < M.v := by
  have hA : 0 < M.p 0 + M.p 1 := by linarith [M.p_pos 0, M.p_pos 1]
  have hB : 0 < M.p 2 + M.p 3 := by linarith [M.p_pos 2, M.p_pos 3]
  have hα : 0 < M.γ * (M.u - 1) := mul_pos M.γ_pos (by linarith [M.one_lt_u])
  have hβ : 0 < M.γ * (1 - M.d) := mul_pos M.γ_pos (by linarith [M.d_lt_one])
  set A := M.p 0 + M.p 1
  set B := M.p 2 + M.p 3
  set α := M.γ * (M.u - 1)
  set β := M.γ * (1 - M.d)
  set a0 := Real.log (α * A / (β * B)) / (α + β)
  have hg : ∀ a, ∫ ω, Real.exp (-M.γ * a * (M.Rt ω - 1)) ∂M.P =
      A * Real.exp (-α * a) + B * Real.exp (β * a) := integral_eq M
  have hv : M.v = A * Real.exp (-α * a0) + B * Real.exp (β * a0) := by
    unfold Market.v
    simp_rw [hg]
    apply le_antisymm
    · exact ciInf_le ⟨0, by rintro _ ⟨a, rfl⟩; positivity⟩ a0
    · exact le_ciInf (fun a => key A B α β hA hB hα hβ a)
  refine ⟨⟨a0, by rw [hg, hv]⟩, ?_⟩
  rw [hv]; positivity
