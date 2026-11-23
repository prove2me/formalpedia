-- Prove2me | solution 1 for Formalism.DimensionVariation.fjOrth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:59.587273+00:00
-- url     : https://prove2.me/submissions/369353b6-3a05-4cd0-9603-e7bdc8e94ff9

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
namespace Formalism.DimensionVariation
private theorem integral_comp_mul_of_norm_eq_one (g : ℂ → ℂ) (w : ℂ) (hw : ‖w‖ = 1) :
    ∫ z : ℂ, g (w * z) = ∫ z : ℂ, g z := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hw
    exact zero_ne_one hw
  let L : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => w * z
      invFun := fun z => w⁻¹ * z
      map_add' := fun x y => mul_add w x y
      map_smul' := fun r z => mul_smul_comm r w z
      left_inv := fun z => inv_mul_cancel_left₀ hw0 z
      right_inv := fun z => mul_inv_cancel_left₀ hw0 z
      norm_map' := fun z => by
        show ‖w * z‖ = ‖z‖
        rw [norm_mul, hw, one_mul] }
  exact L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding g
end Formalism.DimensionVariation
end
end

set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution (N a b : ℕ) (hab : a ≠ b) : ∫ z : ℂ, fjChi N z * fjW a b z = 0 := by
  have hab' : ((a : ℝ) - b) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  obtain ⟨θ, hθπ⟩ : ∃ θ : ℝ, ((a : ℂ) - b) * (θ : ℂ) = π := by
    refine ⟨π / ((a : ℝ) - b), ?_⟩
    have h : ((a : ℝ) - b) * (π / ((a : ℝ) - b)) = π := by field_simp
    exact_mod_cast h
  obtain ⟨w, hw1, hwab⟩ : ∃ w : ℂ, ‖w‖ = 1 ∧ w ^ a * conj w ^ b = -1 := by
    refine ⟨Complex.exp (θ * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_⟩
    rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_pi_mul_I]
    congr 1
    linear_combination Complex.I * hθπ
  have hpt : ∀ z : ℂ, fjChi N (w * z) * fjW a b (w * z) =
      -(fjChi N z * fjW a b z) := by
    intro z
    have hn : ‖w * z‖ = ‖z‖ := by rw [norm_mul, hw1, one_mul]
    have hc : conj (w * z) = conj w * conj z := map_mul _ _ _
    simp only [fjChi, fjW]
    rw [hn, hc, mul_pow, mul_pow]
    linear_combination ((if ‖z‖ ≤ (N : ℝ) then (1 : ℂ) else 0) *
      (z ^ a * conj z ^ b * (Real.exp (-‖z‖ ^ 2) : ℂ))) * hwab
  have h := integral_comp_mul_of_norm_eq_one
    (fun z => fjChi N z * fjW a b z) w hw1
  have h2 : ∫ z : ℂ, fjChi N (w * z) * fjW a b (w * z) =
      -∫ z : ℂ, fjChi N z * fjW a b z := by
    simp_rw [hpt]
    exact integral_neg _
  have h3 : (∫ z : ℂ, fjChi N z * fjW a b z) =
      -∫ z : ℂ, fjChi N z * fjW a b z := h.symm.trans h2
  linear_combination h3 / 2
end Formalism.DimensionVariation
