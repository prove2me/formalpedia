-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.avgLimit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:59.533385+00:00
-- url     : https://prove2.me/submissions/1500e65b-e613-4ff1-be09-e3b11b2fc1a8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_RootNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_rootNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_rootAvg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_ratioLim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution {n : ℕ} (y : Fin n → ℂ) (hy : ∀ i, ‖y i‖ ≠ 1) (j : ℕ) (hj : 1 ≤ j) (K : ℝ)
    (hK : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ j / (1 - y i * ζ)‖ ≤ K) :
    ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) ≤ K := by

  classical
  have hbound : ∀ N : ℕ, j < N → ‖∑ i, y i ^ N / (1 - y i ^ N)‖ ≤ K := by
    intro N hjN
    have hN : 0 < N := by omega
    have h1 : ∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k) = N * ∑ i, y i ^ N / (1 - y i ^ N) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => rootAvg N j hj hjN (y i) (hy i))
    have h2 : ‖∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ ≤ N * K := by
      calc _ ≤ ∑ k ∈ range N, ‖∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
            (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ range N, K := Finset.sum_le_sum (fun k _ => hK _ (rootNorm N hN k))
        _ = N * K := by simp
    rw [h1, norm_mul, Complex.norm_natCast] at h2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact le_of_mul_le_mul_left h2 hNpos
  have hlim : Tendsto (fun N : ℕ => ∑ i, y i ^ N / (1 - y i ^ N)) atTop
      (𝓝 (∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0)) :=
    tendsto_finset_sum _ (fun i _ => ratioLim (y i) (hy i))
  have hle : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ ≤ K := by
    apply le_of_tendsto hlim.norm
    rw [Filter.eventually_atTop]
    exact ⟨j + 1, fun N hN => hbound N (by omega)⟩
  have hval : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ = ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, norm_mul, norm_neg,
      norm_one, mul_one, Complex.norm_natCast]
  rw [← hval]
  exact hle
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
