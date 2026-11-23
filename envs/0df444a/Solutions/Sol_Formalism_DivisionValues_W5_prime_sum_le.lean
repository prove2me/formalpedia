-- Prove2me | solution 1 for Formalism.DivisionValues.W5.prime_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:30.333114+00:00
-- url     : https://prove2.me/submissions/aebd085f-e194-4c9f-8a9d-52afb69ac952

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_head_num
import Theorems.Thm_Formalism_DivisionValues_W5_head_sum
import Theorems.Thm_Formalism_DivisionValues_W5_blk
import Theorems.Thm_Formalism_DivisionValues_W5_aux_statement_15
import Theorems.Thm_Formalism_DivisionValues_W5_term_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.W5
namespace Formalism.DivisionValues.W5
theorem _root_.solution (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 4995 / 10000 := by
  classical
  obtain ⟨K, hK40, hK⟩ : ∃ K : ℕ, 40 ≤ K ∧ ∀ p ∈ s, p < 6 * K := by
    refine ⟨s.sup id + 40, by omega, fun p hp => ?_⟩
    have : p ≤ s.sup id := Finset.le_sup (f := id) hp
    omega
  rw [← Finset.sum_filter_add_sum_filter_not s (fun p => p < 240)]
  have hhead : ∑ p ∈ s.filter (fun p => p < 240), Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.range 240, (if n.Prime then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hp.2, hs p hp.1⟩
    · intro n _ _
      exact term_nonneg n
  have htail : ∑ p ∈ s.filter (fun p => ¬ p < 240), Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Ico 240 (6 * K),
        (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, hK p hp.1⟩,
        aux_statement_15 p (hs p hp.1) (by omega)⟩
    · intro n _ _
      exact term_nonneg n
  have hb := blk K hK40
  have hpos : 0 ≤ (Real.log ((6 * K : ℕ) - 6 : ℝ) + 1) / ((6 * K : ℕ) - 6 : ℝ) := by
    have h1 : (234 : ℝ) ≤ ((6 * K : ℕ) : ℝ) - 6 := by
      have : (240 : ℝ) ≤ ((6 * K : ℕ) : ℝ) := by exact_mod_cast (by omega : 240 ≤ 6 * K)
      linarith
    apply div_nonneg _ (by linarith)
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ ((6 * K : ℕ) : ℝ) - 6)
    linarith
  rw [head_sum] at hhead
  have hn := head_num
  linarith
end Formalism.DivisionValues.W5
