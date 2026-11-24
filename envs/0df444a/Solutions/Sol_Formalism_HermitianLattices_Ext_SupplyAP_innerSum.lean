-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.innerSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:33.653516+00:00
-- url     : https://prove2.me/submissions/a65fcc45-3b2d-44bb-8736-182956bfa256

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_geomIcc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (x : ℝ) (hx : 0 < x) (d N : ℕ) (hd : 1 ≤ d) :
    ∃ T : ℝ, 0 ≤ T ∧ T ≤ (x + 1) * Real.exp (-(N : ℝ) / x) ∧
      ∑ m ∈ Icc 1 (N / d), Real.exp (-((d * m : ℕ) : ℝ) / x) = x / d + gExp ((d : ℝ) / x) - T := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set t : ℝ := (d : ℝ) / x with ht
  have ht0 : 0 < t := div_pos hd0 hx
  set u : ℝ := Real.exp (-t) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u < 1 := by
    rw [hu, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1u : 0 < 1 - u := by linarith
  have hterm : ∀ m : ℕ, Real.exp (-((d * m : ℕ) : ℝ) / x) = u ^ m := by
    intro m
    rw [hu, ← Real.exp_nat_mul]
    congr 1
    rw [ht]; push_cast; field_simp
  refine ⟨u ^ (N / d + 1) / (1 - u), by positivity, ?_, ?_⟩
  ·
    have hA : u ^ (N / d + 1) ≤ Real.exp (-(N : ℝ) / x) := by
      rw [← hterm]
      apply Real.exp_le_exp.mpr
      have : N < d * (N / d + 1) := Nat.lt_mul_div_succ N hd
      have h2 : (N : ℝ) ≤ ((d * (N / d + 1) : ℕ) : ℝ) := by exact_mod_cast this.le
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_right h2 hx.le)
    have hB : 1 / (x + 1) ≤ 1 - u := by
      have hle : u ≤ Real.exp (-(1 / x)) := by
        rw [hu]; apply Real.exp_le_exp.mpr
        rw [ht]; exact neg_le_neg (div_le_div_of_nonneg_right hd1 hx.le)
      have h3 : 1 / x + 1 ≤ Real.exp (1 / x) := Real.add_one_le_exp _
      have h4 : Real.exp (-(1 / x)) ≤ x / (x + 1) := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
        calc (x / (x + 1))⁻¹ = 1 / x + 1 := by field_simp; ring
          _ ≤ _ := h3
      have h5 : 1 - x / (x + 1) = 1 / (x + 1) := by field_simp; ring
      linarith
    rw [div_le_iff₀ h1u]
    have hE : 0 < Real.exp (-(N : ℝ) / x) := Real.exp_pos _
    have hx1 : 0 < x + 1 := by linarith
    have h6 : 1 ≤ (x + 1) * (1 - u) := by
      rw [div_le_iff₀ hx1] at hB; linarith
    calc u ^ (N / d + 1) ≤ Real.exp (-(N : ℝ) / x) := hA
      _ = Real.exp (-(N : ℝ) / x) * 1 := by ring
      _ ≤ Real.exp (-(N : ℝ) / x) * ((x + 1) * (1 - u)) := by
        exact mul_le_mul_of_nonneg_left h6 hE.le
      _ = _ := by ring
  · simp_rw [hterm]
    rw [geomIcc u hu1.ne]
    have hg : x / d + gExp t = u / (1 - u) := by
      unfold gExp
      have : (1 : ℝ) / t = x / d := by rw [ht]; field_simp
      rw [this]
      have he : Real.exp t = u⁻¹ := by rw [hu, Real.exp_neg, inv_inv]
      rw [he]
      have hu' : u ≠ 0 := hu0.ne'
      have : u⁻¹ - 1 ≠ 0 := by
        have : u⁻¹ - 1 = (1 - u) / u := by field_simp
        rw [this]; positivity
      field_simp
      ring
    rw [hg]
    ring
end Formalism.HermitianLattices.Ext.SupplyAP
