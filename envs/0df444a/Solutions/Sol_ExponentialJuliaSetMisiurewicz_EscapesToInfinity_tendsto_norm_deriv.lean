-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.EscapesToInfinity.tendsto_norm_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:47.496258+00:00
-- url     : https://prove2.me/submissions/ec4d6861-1448-4a13-aa1e-92d81d66309c

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_ExpChaotic_Dynamics
import Definitions.Def_ExpChaotic_PaperConsequences
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_deriv_expIterate_ne_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_deriv_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
namespace EscapesToInfinity
theorem _root_.solution {z : ℂ} (hz : EscapesToInfinity z) :
    Tendsto (fun n => ‖deriv (expIterate n) z‖) atTop atTop := by
  obtain ⟨N, hN⟩ := hz 2
  have hd : 0 < ‖deriv (expIterate N) z‖ := norm_pos_iff.mpr (deriv_expIterate_ne_zero N z)
  have hgrowth : ∀ k : ℕ,
      ‖deriv (expIterate N) z‖ * 2 ^ k ≤ ‖deriv (expIterate (N + k)) z‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, deriv_expIterate_succ, norm_mul, pow_succ]
      calc
        ‖deriv (expIterate N) z‖ * (2 ^ k * 2)
            = (‖deriv (expIterate N) z‖ * 2 ^ k) * 2 := by ring
        _ ≤ ‖deriv (expIterate (N + k)) z‖ *
            ‖Complex.exp (expIterate (N + k) z)‖ :=
          mul_le_mul ih (by simpa only [← expIterate_succ] using hN (N + k + 1) (by omega))
            (by norm_num) (norm_nonneg _)
  have ht := tendsto_atTop_mono hgrowth
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hd)
  exact (tendsto_add_atTop_iff_nat N).mp (by simpa only [Nat.add_comm] using ht)
end EscapesToInfinity
end ExponentialJuliaSetMisiurewicz
