-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.exists_power_sum_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:52.20725+00:00
-- url     : https://prove2.me/submissions/385d782a-d0af-44c5-92c8-060ffa7c41b3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (C : ℝ) (a : ℕ) (hC : 0 < C)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ j n : ℕ, m + 1 ≤ j ∧ j ≤ m + a * n ∧ 1 ≤ n ∧ (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re ∧
      (1 / 2) ^ j * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤
        ‖∑ i, u i ^ j‖ + ε ^ (j - 2) * ∑ i, (u i).re := by
  classical
  have hre0 : ∀ i, 0 ≤ (u i).re := fun i => le_trans (sq_nonneg _) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := by
      first
        | exact Complex.re_le_norm (u i)
        | exact Complex.re_le_abs (u i)
    nlinarith [norm_nonneg (u i)]
  obtain ⟨i0, hi0⟩ := hi

  set I := Finset.univ.filter (fun i => ε ≤ ‖u i‖) with hIdef
  have hi0I : i0 ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩
  have hIne : I.Nonempty := ⟨i0, hi0I⟩
  obtain ⟨i1, hi1I, hi1⟩ := Finset.exists_mem_eq_sup' hIne (fun i => ‖u i‖)
  set r := I.sup' hIne (fun i => ‖u i‖) with hr
  have hr0 : 1 / 2 ≤ r := le_trans hi0 (Finset.le_sup' (fun i => ‖u i‖) hi0I)
  have hrpos : 0 < r := by linarith
  have hnr : ‖(r : ℂ)‖ = r := by
    first
      | rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      | simp [abs_of_pos hrpos]
  set n := I.card with hn
  have hn1 : 1 ≤ n := Finset.card_pos.2 hIne
  let e : Fin n ≃ I := I.equivFin.symm
  let z : Fin n → ℂ := fun k => u (e k) / r
  have hz1 : ∀ k, ‖z k‖ ≤ 1 := by
    intro k
    simp only [z]
    rw [norm_div, hnr, div_le_one hrpos]
    exact Finset.le_sup' (fun i => ‖u i‖) (e k).2
  have hz2 : ∃ k, ‖z k‖ = 1 := by
    refine ⟨e.symm ⟨i1, hi1I⟩, ?_⟩
    simp only [z, Equiv.apply_symm_apply]
    rw [norm_div, hnr, ← hi1]
    exact div_self hrpos.ne'
  obtain ⟨k, hk1, hk2, hkB⟩ := hT n m z hn1 hz1 hz2

  have hsumz : ∑ k', z k' ^ k = (∑ i ∈ I, u i ^ k) / (r : ℂ) ^ k := by
    simp only [z, div_pow]
    rw [← Finset.sum_div]
    congr 1
    rw [← Finset.sum_coe_sort I]
    exact e.sum_comp (fun i : I => u i ^ k)
  have hB0 : 0 ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hC.le (by positivity))) _
  have hmain : (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i ∈ I, u i ^ k‖ := by
    rw [hsumz, norm_div, norm_pow, hnr, le_div_iff₀ (pow_pos hrpos k)] at hkB
    calc (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n)
        ≤ r ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hr0 k) hB0
      _ ≤ ‖∑ i ∈ I, u i ^ k‖ := by linarith

  have hcompl : ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ε ^ (k - 2) * ∑ i, (u i).re := by
    calc ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ∑ i ∈ Iᶜ, ε ^ (k - 2) * (u i).re := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hlt : ‖u i‖ < ε := by
            rw [Finset.mem_compl, Finset.mem_filter] at hi
            push_neg at hi
            exact hi (Finset.mem_univ _)
          calc ‖u i‖ ^ k = ‖u i‖ ^ 2 * ‖u i‖ ^ (k - 2) := by
                rw [← pow_add]
                congr 1
                omega
            _ ≤ (u i).re * ε ^ (k - 2) :=
                mul_le_mul (hu i) (pow_le_pow_left₀ (norm_nonneg _) hlt.le _) (by positivity) (hre0 i)
            _ = ε ^ (k - 2) * (u i).re := by ring
      _ = ε ^ (k - 2) * ∑ i ∈ Iᶜ, (u i).re := by rw [Finset.mul_sum]
      _ ≤ ε ^ (k - 2) * ∑ i, (u i).re :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i)
            (by positivity)
  have hsplit : ‖∑ i ∈ I, u i ^ k‖ ≤ ‖∑ i, u i ^ k‖ + ∑ i ∈ Iᶜ, ‖u i‖ ^ k := by
    have h := Finset.sum_add_sum_compl I (fun i => u i ^ k)
    have h' : ∑ i ∈ I, u i ^ k = ∑ i, u i ^ k - ∑ i ∈ Iᶜ, u i ^ k := by
      rw [← h]
      ring
    rw [h']
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_pow _ _))
  have hnε : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ I, ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, (u i).re := Finset.sum_le_sum fun i hi =>
          le_trans (pow_le_pow_left₀ hε0.le (Finset.mem_filter.1 hi).2 2) (hu i)
      _ ≤ ∑ i, (u i).re :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i
  refine ⟨k, n, hk1, hk2, hn1, hnε, ?_⟩
  linarith [hmain, hsplit, hcompl]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
