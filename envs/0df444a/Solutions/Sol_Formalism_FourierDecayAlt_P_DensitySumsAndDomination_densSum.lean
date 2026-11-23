-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:15.644012+00:00
-- url     : https://prove2.me/submissions/f1644233-6b39-47b7-9510-14765e30b5d2

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_sq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_pow_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution : DensSum := by
  intro P S q l f n hn hS hf
  have hA : ∀ p ∈ S, (q p ^ n)⁻¹ ≤ (((l p : ℕ) : ℝ) ^ n)⁻¹ := by
    intro p hp
    obtain ⟨hpr, hle⟩ := hS p hp
    have h0 : (0 : ℝ) < (l p : ℝ) := by exact_mod_cast hpr.pos
    exact inv_anti₀ (by positivity) (by gcongr)
  have hB : ∑ p ∈ S, (((l p : ℕ) : ℝ) ^ n)⁻¹ ≤
      (f : ℝ) * ∑ m ∈ S.image l, (((m : ℕ) : ℝ) ^ n)⁻¹ := by
    rw [Finset.sum_comp (fun m : ℕ => (((m : ℕ) : ℝ) ^ n)⁻¹) l, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h := hf m
    first
      | exact_mod_cast h
      | (norm_cast; convert h)
      | norm_cast
  have hC : ∑ m ∈ S.image l, (((m : ℕ) : ℝ) ^ n)⁻¹ ≤
      ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ n)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨p, hp, rfl⟩ := hm
      rw [Finset.mem_Icc]
      have h1 : l p ≤ S.sup l := Finset.le_sup hp
      exact ⟨(hS p hp).1.two_le, by omega⟩
    · intro m _ _
      positivity
  have hD : ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ n)⁻¹ ≤ 3 * ((2 : ℝ) ^ n)⁻¹ := by
    calc ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ n)⁻¹
        ≤ ∑ m ∈ Icc 2 (S.sup l + 2), 4 * ((2 : ℝ) ^ n)⁻¹ * (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun m hm => ?_
          exact pow_bd m n (Finset.mem_Icc.mp hm).1 hn
      _ = 4 * ((2 : ℝ) ^ n)⁻¹ * ∑ m ∈ Icc 2 (S.sup l + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 4 * ((2 : ℝ) ^ n)⁻¹ * (3 / 4 - (((S.sup l : ℕ) : ℝ) + 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (sq_sum _) (by positivity)
      _ ≤ 3 * ((2 : ℝ) ^ n)⁻¹ := by
          have h1 : 0 ≤ (((S.sup l : ℕ) : ℝ) + 2)⁻¹ := by positivity
          have h2 : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
          nlinarith
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  calc ∑ p ∈ S, (q p ^ n)⁻¹ ≤ ∑ p ∈ S, (((l p : ℕ) : ℝ) ^ n)⁻¹ := Finset.sum_le_sum hA
    _ ≤ (f : ℝ) * ∑ m ∈ S.image l, (((m : ℕ) : ℝ) ^ n)⁻¹ := hB
    _ ≤ (f : ℝ) * (3 * ((2 : ℝ) ^ n)⁻¹) := mul_le_mul_of_nonneg_left (hC.trans hD) hf0
    _ = 3 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by ring
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
