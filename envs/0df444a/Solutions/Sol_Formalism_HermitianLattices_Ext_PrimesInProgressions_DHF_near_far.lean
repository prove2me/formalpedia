-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.near_far
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:47.607789+00:00
-- url     : https://prove2.me/submissions/1b6b4b67-34b8-492d-83bb-59e6882e00ba

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution (c : ℝ) (A B : ℕ) (hc : 0 < c)
    (hT : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c ^ K ≤ (∑ i, z i ^ k).re)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (K : ℕ) (hK2 : 2 ≤ K) (hKB : (B : ℝ) * (∑ i, (u i).re) ≤ ε ^ 2 * K) :
    ∃ j : ℕ, K ≤ j ∧ j ≤ A * K ∧
      c ^ K * (1 / 2) ^ j ≤ (∑ i, u i ^ j).re + ε ^ (j - 2) * ∑ i, (u i).re := by
  have hre : ∀ i, 0 ≤ (u i).re := fun i => le_trans (by positivity) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := Complex.re_le_norm _
    nlinarith [norm_nonneg (u i)]
  set near := (univ : Finset (Fin N)).filter (fun i => ε ≤ ‖u i‖) with hnear
  obtain ⟨i0, hi0⟩ := hi
  have hi0n : i0 ∈ near := by simp [hnear]; linarith
  have hne : near.Nonempty := ⟨i0, hi0n⟩
  obtain ⟨is, his, hmax⟩ := near.exists_max_image (fun i => ‖u i‖) hne
  set R := ‖u is‖ with hR
  have hR2 : 1 / 2 ≤ R := le_trans hi0 (hmax i0 hi0n)
  have hR0 : 0 < R := by linarith
  have hR1 : R ≤ 1 := hle1 is
  set n := near.card with hn

  have hcount : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ near, ε ^ 2 := by simp [hn]
      _ ≤ ∑ i ∈ near, ‖u i‖ ^ 2 := by
          apply sum_le_sum; intro i hi
          have : ε ≤ ‖u i‖ := by simpa [hnear] using hi
          exact pow_le_pow_left₀ hε0.le this 2
      _ ≤ ∑ i ∈ near, (u i).re := sum_le_sum (fun i _ => hu i)
      _ ≤ ∑ i, (u i).re := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hre i)
  have hBn : B * n ≤ K := by
    have h1 : (B : ℝ) * n * ε ^ 2 ≤ ε ^ 2 * K := by
      calc (B : ℝ) * n * ε ^ 2 = B * (n * ε ^ 2) := by ring
        _ ≤ B * ∑ i, (u i).re := mul_le_mul_of_nonneg_left hcount (by positivity)
        _ ≤ _ := hKB
    have h2 : (B : ℝ) * n ≤ K := by
      have : 0 < ε ^ 2 := by positivity
      nlinarith
    exact_mod_cast h2
  have hn1 : 1 ≤ n := Finset.card_pos.mpr hne
  let e := near.equivFin
  let z : Fin n → ℂ := fun k => u (e.symm k) / (R : ℂ)
  have hz : ∀ k, z k = u (e.symm k) / (R : ℂ) := fun k => rfl
  have hzn : ∀ k, ‖z k‖ = ‖u (e.symm k)‖ / R := by
    intro k; rw [hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
  obtain ⟨j, hKj, hjA, hj⟩ := hT n K z hn1 hBn
    (by
      intro k; rw [hzn, div_le_one hR0]
      exact hmax _ (e.symm k).2)
    (by
      refine ⟨e ⟨is, his⟩, ?_⟩
      rw [hzn]; simp [R, div_self (ne_of_gt hR0)])
    (by
      intro k
      rw [hzn, hz, Complex.div_ofReal_re]
      have h1 := hu (e.symm k)
      have h2 : ‖u (e.symm k)‖ ≤ R := hmax _ (e.symm k).2
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc ‖u (e.symm k)‖ ^ 2 ≤ (u (e.symm k)).re := h1
        _ ≤ 2 * ((u (e.symm k)).re / R) * R ^ 2 := by
          rw [show 2 * ((u (e.symm k)).re / R) * R ^ 2 = (u (e.symm k)).re * (2 * R) by
            field_simp]
          have : 1 ≤ 2 * R := by linarith
          nlinarith [hre (e.symm k)])
  refine ⟨j, hKj, hjA, ?_⟩

  have hsumz : (∑ k, z k ^ j) * (R : ℂ) ^ j = ∑ i ∈ near, u i ^ j := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_coe_sort near (fun i => u i ^ j)]
    rw [← e.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [hz, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ (by exact_mod_cast hR0.ne')
  have hnear_re : c ^ K * (1 / 2) ^ j ≤ (∑ i ∈ near, u i ^ j).re := by
    rw [← hsumz, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have : (1 / 2 : ℝ) ^ j ≤ R ^ j := pow_le_pow_left₀ (by norm_num) hR2 j
    have hcK : 0 < c ^ K := pow_pos hc K
    nlinarith [pow_pos hR0 j]
  have hfar : -(ε ^ (j - 2) * ∑ i, (u i).re) ≤ (∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), u i ^ j).re := by
    rw [Complex.re_sum]
    have hj2 : 2 ≤ j := le_trans hK2 hKj
    have : ∀ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), -(ε ^ (j - 2) * (u i).re) ≤ (u i ^ j).re := by
      intro i hi
      have hlt : ‖u i‖ < ε := by simpa using hi
      have h1 : -(u i ^ j).re ≤ ‖u i‖ ^ j := by
        have := Complex.abs_re_le_norm (u i ^ j); rw [norm_pow] at this
        linarith [neg_abs_le (u i ^ j).re]
      have h2 : ‖u i‖ ^ j = ‖u i‖ ^ (j - 2) * ‖u i‖ ^ 2 := by
        rw [← pow_add]; congr 1; omega
      have h3 : ‖u i‖ ^ (j - 2) ≤ ε ^ (j - 2) := pow_le_pow_left₀ (norm_nonneg _) hlt.le _
      have h4 : ‖u i‖ ^ (j - 2) * ‖u i‖ ^ 2 ≤ ε ^ (j - 2) * (u i).re :=
        mul_le_mul h3 (hu i) (by positivity) (by positivity)
      linarith
    calc -(ε ^ (j - 2) * ∑ i, (u i).re) ≤ -(ε ^ (j - 2) * ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), (u i).re) := by
          have : ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), (u i).re ≤ ∑ i, (u i).re :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hre i)
          have : 0 ≤ ε ^ (j - 2) := by positivity
          nlinarith
      _ = ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), -(ε ^ (j - 2) * (u i).re) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ _ := sum_le_sum this
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin N)) (fun i => ε ≤ ‖u i‖) (fun i => u i ^ j)
  have hnr : (∑ x ∈ univ.filter (fun x => ε ≤ ‖u x‖), u x ^ j) = ∑ i ∈ near, u i ^ j := rfl
  rw [← hsplit, Complex.add_re, hnr]
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
