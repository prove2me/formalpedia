-- Prove2me | solution 1 for FirstPassageLinearTransport.normalizedCorrection_scaled_le_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:57.62519+00:00
-- url     : https://prove2.me/submissions/5d6bdfd9-d3f9-4f9c-a59d-33df45f7964b

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_rho_pos
import Theorems.Thm_FirstPassageLinearTransport_rho_lt_one
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrectionTerm_scaled_le_maximal
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n M k : ℕ} {h : ℝ}
    (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (2 + Real.sqrt 3) * (3 : ℝ) ^ h := by
  have hterm :
      ∀ i ∈ Finset.range k,
        normalizedCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i) := by
    intro i hi
    exact normalizedCorrectionTerm_scaled_le_maximal
      (Finset.mem_range.mp hi) hkM hreg
  have hsum :
      normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ h / 2 * ∑ j ∈ Finset.range k, rho ^ j := by
    calc
      normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) =
          ∑ i ∈ Finset.range k,
            normalizedCorrectionTerm k n i *
              (3 : ℝ) ^ ((k : ℝ) / 2) := by
        simp only [normalizedCorrection, Finset.sum_mul]
      _ ≤ ∑ i ∈ Finset.range k,
          ((3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i)) :=
        Finset.sum_le_sum hterm
      _ = (3 : ℝ) ^ h / 2 *
          ∑ j ∈ Finset.range k, rho ^ (k - 1 - j) := by
        rw [Finset.mul_sum]
      _ = (3 : ℝ) ^ h / 2 *
          ∑ j ∈ Finset.range k, rho ^ j := by
        rw [Finset.sum_range_reflect]
  have hgeom :
      ∑ j ∈ Finset.range k, rho ^ j < (1 - rho)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ (sub_pos.mpr rho_lt_one)]
    rw [geom_sum_mul_neg]
    have hpow : 0 < rho ^ k := pow_pos rho_pos k
    linarith
  have hconstant : ((1 - rho)⁻¹ : ℝ) = 2 * (2 + Real.sqrt 3) := by
    unfold rho
    have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hden : 2 - Real.sqrt 3 ≠ 0 := by
      nlinarith [rho_lt_one]
    field_simp
    nlinarith
  calc
    _ ≤ (3 : ℝ) ^ h / 2 * ∑ j ∈ Finset.range k, rho ^ j := hsum
    _ ≤ (3 : ℝ) ^ h / 2 * (1 - rho)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeom.le (by positivity)
    _ = (2 + Real.sqrt 3) * (3 : ℝ) ^ h := by
      rw [hconstant]
      ring
end FirstPassageLinearTransport
