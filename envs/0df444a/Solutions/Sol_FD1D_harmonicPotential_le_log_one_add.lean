-- Prove2me | solution 1 for FD1D.harmonicPotential_le_log_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:45.639946+00:00
-- url     : https://prove2.me/submissions/fb2345f7-2aff-4d2a-8111-0c6193dbb49b

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_succ
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_leafCount_eq_pow
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.leafCount_eq_pow
attribute [local simp] FD1D.natFloor_parameterRatio
attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
namespace FD1D
theorem _root_.solution {a : ℝ} (ha : 0 < a) (k : ℕ) :
    harmonicPotential a k ≤ Real.log (1 + (k : ℝ) / a) := by
  have hanti :
      AntitoneOn (fun x : ℝ => (a + x)⁻¹)
        (Icc 0 ((0 : ℝ) + (k : ℝ))) := by
    intro x hx y hy hxy
    exact (inv_le_inv₀ (add_pos_of_pos_of_nonneg ha hy.1)
      (add_pos_of_pos_of_nonneg ha hx.1)).2 (by linarith)
  have hsum :
      (∑ i ∈ Finset.range k, (a + (i + 1 : ℕ))⁻¹) ≤
        ∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹ := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      hanti.sum_le_integral (x₀ := (0 : ℝ)) (a := k)
  have hpot :
      harmonicPotential a k =
        ∑ i ∈ Finset.range k, (a + (i + 1 : ℕ))⁻¹ := by
    clear hanti hsum
    induction k with
    | zero => simp
    | succ k ih =>
        rw [harmonicPotential_succ, Finset.sum_range_succ, ih]
        congr 1
        simp only [Nat.cast_add, Nat.cast_one]
        ring
  have hint :
      (∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹) =
        Real.log (1 + (k : ℝ) / a) := by
    calc
      (∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹) =
          ∫ x in a..a + k, x⁻¹ := by
            simpa [add_comm] using
              (integral_comp_add_left (fun x : ℝ => x⁻¹) a :
                (∫ x in (0 : ℝ)..(k : ℝ), (a + x)⁻¹) =
                  ∫ x in a + 0..a + k, x⁻¹)
      _ = Real.log ((a + k) / a) :=
        integral_inv_of_pos ha (by positivity)
      _ = Real.log (1 + (k : ℝ) / a) := by
        congr 1
        field_simp
  rw [hpot]
  exact hsum.trans_eq hint
end FD1D
