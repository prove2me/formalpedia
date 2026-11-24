-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_wsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:28.171823+00:00
-- url     : https://prove2.me/submissions/5c571095-5e03-419e-8d36-463bbfdad3cc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_pow_exp_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_one_sub_exp_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_pow_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) / η ^ (m + 1) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / ((m:ℝ) + 1) := ⟨_, rfl⟩
  have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hm1ne : (m:ℝ) + 1 ≠ 0 := hm1.ne'
  have hδη : ((m:ℝ) + 1) * δ = η := by rw [hδ]; field_simp
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hη hm1
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hη'nn : 0 ≤ (m:ℝ) * δ := mul_nonneg hm0 hδpos.le
  have hsplit : (m:ℝ) * δ + δ = η := by rw [← hδη]; ring
  have hη'le : (m:ℝ) * δ ≤ 1 := by linarith
  have hpow : η ^ m ≤ Real.exp 1 * ((m:ℝ) * δ) ^ m := by
    rw [← hδη, mul_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (dhpr_pow_ratio m) (pow_nonneg hδpos.le m)
  have hterm : ∀ v : ℕ, η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) ≤
      Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
    intro v
    have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
    have h1 := dhpr_pow_exp_le m hη'nn ht
    have hexp : Real.exp (-(η * v)) ≤
        Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← hsplit]
      have e : -(((m:ℝ) * δ + δ) * (v:ℝ)) =
          1 + -((m:ℝ) * δ * ((v:ℝ) + 1)) + -(δ * v) - (1 - (m:ℝ) * δ) := by ring
      rw [e]; linarith
    calc η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v)))
        ≤ (Real.exp 1 * ((m:ℝ) * δ) ^ m) * (((v:ℝ) + 1) ^ m *
            (Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)))) := by
          refine mul_le_mul hpow ?_ (by positivity) (mul_nonneg (Real.exp_pos 1).le (pow_nonneg hη'nn m))
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 1 * Real.exp 1 * (((m:ℝ) * δ) ^ m * (((v:ℝ) + 1) ^ m *
            Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))))) * Real.exp (-(δ * v)) := by ring
      _ ≤ Real.exp 1 * Real.exp 1 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          rw [← Real.exp_add]; norm_num
  have hsum : η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun v _ => hterm v)
  have hG : (∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ ≤ 1 + δ := by
    have hrw : ∀ v : ℕ, Real.exp (-(δ * v)) = Real.exp (-δ) ^ v := by
      intro v; rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [hrw]
    have hr0 : 0 < Real.exp (-δ) := Real.exp_pos _
    have hsub : ∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Ico] at hx
        rw [Finset.mem_range]
        exact hx.2
      · intro i _ _
        exact pow_nonneg hr0.le i
    have hG0 : 0 ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have hgeo : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) ≤ 1 := by
      have h := geom_sum_mul (Real.exp (-δ)) V
      have hV : 0 ≤ Real.exp (-δ) ^ V := pow_nonneg hr0.le V
      have e : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) =
          -((∑ v ∈ range V, Real.exp (-δ) ^ v) * (Real.exp (-δ) - 1)) := by ring
      rw [e, h]; linarith
    have h2 := dhpr_one_sub_exp_neg hδpos
    have h2' : δ ≤ (1 - Real.exp (-δ)) * (1 + δ) := by
      rwa [div_le_iff₀ (by linarith)] at h2
    calc (∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v) * δ
        ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * δ := mul_le_mul_of_nonneg_right hsub hδpos.le
      _ ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * ((1 - Real.exp (-δ)) * (1 + δ)) :=
          mul_le_mul_of_nonneg_left h2' hG0
      _ = ((∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ))) * (1 + δ) := by ring
      _ ≤ 1 * (1 + δ) := mul_le_mul_of_nonneg_right hgeo (by linarith)
      _ = 1 + δ := one_mul _
  rw [le_div_iff₀ (pow_pos hη (m + 1))]
  calc (∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η ^ (m + 1)
      = (η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η := by ring
    _ ≤ (Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * η :=
        mul_le_mul_of_nonneg_right hsum hη.le
    _ = Real.exp 2 * (m.factorial : ℝ) * ((∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ) *
          ((m:ℝ) + 1) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (1 + δ) * ((m:ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hm1.le
        exact mul_le_mul_of_nonneg_left hG (by positivity)
    _ = Real.exp 2 * (m.factorial : ℝ) * ((m:ℝ) + 1 + η) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (2 * ((m:ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
