-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.finiteShort_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:56.968183+00:00
-- url     : https://prove2.me/submissions/906e9cc3-5d14-410d-a3fa-aa4e1e91e1ec

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinD
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_whiten_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open Matrix
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution : FiniteShortStatement := by
  intro d G hG B
  obtain ⟨R, hRu, hGR⟩ := whiten_holds d G hG
  set A : ℝ := ∑ i, ∑ j, |R⁻¹ i j| with hA
  set M : ℤ := ⌈A * (1 + B)⌉ with hM
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-M) M) fun _ => Set.finite_Icc _ _).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro i
  set cv : Fin d → ℝ := fun i => (c i : ℝ) with hcv
  set y : Fin d → ℝ := R *ᵥ cv with hy
  have hyy : ∑ j, y j * y j ≤ B := by
    have e : cv ⬝ᵥ (G *ᵥ cv) = y ⬝ᵥ y := by
      rw [hGR, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [e] at hc
    simpa [dotProduct] using hc
  have hyj : ∀ j, |y j| ≤ 1 + B := by
    intro j
    have h1 : y j * y j ≤ ∑ k, y k * y k :=
      Finset.single_le_sum (f := fun k => y k * y k) (fun k _ => mul_self_nonneg (y k)) (Finset.mem_univ j)
    have h2 : |y j| ≤ 1 + y j * y j := by
      nlinarith [abs_nonneg (y j), sq_abs (y j), abs_mul_abs_self (y j)]
    linarith
  have hB : 0 ≤ 1 + B := (abs_nonneg _).trans (hyj i)
  have hcvR : cv = R⁻¹ *ᵥ y := by
    rw [hy, mulVec_mulVec, nonsing_inv_mul R hRu, one_mulVec]
  have hci : |cv i| ≤ A * (1 + B) := by
    have e : cv i = ∑ j, R⁻¹ i j * y j := by
      rw [hcvR]
      rfl
    rw [e]
    calc |∑ j, R⁻¹ i j * y j| ≤ ∑ j, |R⁻¹ i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |R⁻¹ i j| * |y j| := by simp only [abs_mul]
      _ ≤ ∑ j, |R⁻¹ i j| * (1 + B) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hyj j) (abs_nonneg _)
      _ = (∑ j, |R⁻¹ i j|) * (1 + B) := by rw [Finset.sum_mul]
      _ ≤ A * (1 + B) := by
          refine mul_le_mul_of_nonneg_right ?_ hB
          exact Finset.single_le_sum (f := fun i => ∑ j, |R⁻¹ i j|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hle : ((|c i| : ℤ) : ℝ) ≤ (M : ℝ) := by
    rw [Int.cast_abs]
    exact hci.trans (Int.le_ceil _)
  have hle' : |c i| ≤ M := by exact_mod_cast hle
  exact abs_le.1 hle'
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
