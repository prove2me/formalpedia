-- Prove2me | solution 1 for BlockCycleRotation.tendsto_riemann_fBar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:02:57.601768+00:00
-- url     : https://prove2.me/submissions/34bf4fa7-9bc8-4c47-9a40-c2154e50b0dc

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_fBar_hasBoxIntegral
import Theorems.Thm_BlockCycleRotation_integralSum_prepartition
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem Inn_zero : Inn 0 = 0 := by simp [Inn]

theorem psi_zero : psi 0 = 0 := by
  unfold psi
  have h : ∀ i, psiTerm 0 i = 0 := by
    intro i
    unfold psiTerm
    have : Inn^[i] (0 : ℝ) = 0 := by
      induction i with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, Inn_zero]
    rw [this, mul_zero]
  simp [h]

theorem fBar_eq_fCost {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : fBar x = fCost x := by
  unfold fBar; rw [if_pos ⟨hx0, hx⟩]

theorem coe_unitBox : (unitBox : Set (Fin 1 → ℝ)) = (fun v : Fin 1 → ℝ => v 0) ⁻¹' Set.Ioc 0 1 := by
  ext v
  rw [Box.mem_coe, Box.mem_def]
  constructor
  · intro h; exact h 0
  · intro h i
    have : i = 0 := Subsingleton.elim _ _
    rw [this]; exact h

theorem measurePreserving_eval :
    MeasureTheory.MeasurePreserving (fun v : Fin 1 → ℝ => v 0) volume volume := by
  have h := MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  exact h

/-- The Riemann integral of `f` over the unit box is `∫₀¹ f`. -/
theorem integral_unitBox :
    ∫ v in (unitBox : Set (Fin 1 → ℝ)), FBar v = ∫ x in (0 : ℝ)..1, fBar x := by
  rw [coe_unitBox, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact measurePreserving_eval.setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding fBar _

theorem unitBox_hasIntegralVertices : hasIntegralVertices unitBox :=
  ⟨fun _ => 0, fun _ => 1, fun _ => by simp [unitBox], fun _ => by simp [unitBox]⟩

theorem fBar_zero : fBar 0 = 1 := by
  rw [fBar_eq_fCost (le_refl 0) (by norm_num), fCost]
  norm_num [psi_zero]

theorem fBar_one : fBar 1 = 1 := by
  rw [fBar_eq_fCost (by norm_num) (le_refl 1), fCost]
  norm_num [psi_zero]

theorem sum_shift_eq {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ Finset.range n, fBar (((j : ℝ) + 1) / (n : ℝ))
      = ∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ∀ j : ℕ, (((j + 1 : ℕ) : ℝ)) / (n : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by
    intro j; push_cast; ring
  have h := Finset.sum_range_succ' (fun k : ℕ => fBar ((k : ℝ) / (n : ℝ))) n
  have h2 := Finset.sum_range_succ (fun k : ℕ => fBar ((k : ℝ) / (n : ℝ))) n
  have h0 : fBar (((0 : ℕ) : ℝ) / (n : ℝ)) = 1 := by norm_num [fBar_zero]
  have h1 : fBar (((n : ℕ) : ℝ) / (n : ℝ)) = 1 := by
    rw [div_self (ne_of_gt hnR)]; exact fBar_one
  rw [h0] at h
  rw [h1] at h2
  have hleft : ∑ j ∈ Finset.range n, fBar ((((j + 1 : ℕ)) : ℝ) / (n : ℝ))
      = ∑ j ∈ Finset.range n, fBar (((j : ℝ) + 1) / (n : ℝ)) :=
    Finset.sum_congr rfl fun j _ => by rw [hcast j]
  rw [← hleft]
  linarith [h, h2]

end BlockCycleRotation

open BlockCycleRotation in
/-- **The evenly spaced Riemann sums converge**, by instantiating Riemann
integrability at the uniform subdivision. -/
theorem solution :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ))) / (n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, fBar x)):= by
  rw [← integral_unitBox]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨r, hr₁, hr₂⟩ := (hasIntegral_iff.mp fBar_hasBoxIntegral) (ε / 2) (half_pos hε)
  refine ⟨max 1 ⌈((r 0 0 : ℝ))⁻¹⌉₊, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : 0 < n := hn1
  have : NeZero n := ⟨by omega⟩
  rw [← sum_shift_eq hn0, ← integralSum_prepartition n]
  refine lt_of_le_of_lt (hr₂ 0 _ ⟨?_, fun _ => ?_, fun h => ?_, fun h => ?_⟩
    (unitPartition.prepartition_isPartition _ unitBox_hasIntegralVertices))
    (half_lt_self_iff.mpr hε)
  · rw [show r 0 = fun _ => r 0 0 from funext_iff.mpr (hr₁ 0 rfl)]
    apply unitPartition.prepartition_isSubordinate n unitBox
    rw [one_div, inv_le_comm₀ (by exact_mod_cast hn0) (r 0 0).prop]
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_max_right _ _) hn))
  · exact unitPartition.prepartition_isHenstock n unitBox
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
