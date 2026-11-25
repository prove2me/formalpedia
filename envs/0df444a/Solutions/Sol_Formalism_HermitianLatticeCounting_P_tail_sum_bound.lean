-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.tail_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:05:23.273029+00:00
-- url     : https://prove2.me/submissions/e00f375c-8182-4f59-a0c1-77e63bd06859

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_tele
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_geo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : TailSum := by
  unfold TailSum
  let g : ℕ × ℕ → ℝ := fun p => (((p.1 : ℝ) + 2) ^ (p.2 + 2))⁻¹
  have hg0 : 0 ≤ g := fun p => by simp only [g, Pi.zero_apply]; positivity
  have hs : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨fun n => (s5a4_geo n).summable, ?_⟩
    have : (fun n : ℕ => ∑' i : ℕ, g (n, i)) = fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      ext n; exact (s5a4_geo n).tsum_eq
    rw [this]; exact s5a4_tele.summable
  have hv : HasSum g 1 := by
    have h1 := hs.hasSum.prod_fiberwise (fun n => s5a4_geo n)
    have h2 := hs.hasSum
    rwa [h1.unique s5a4_tele] at h2
  have hsw : HasSum (fun p : ℕ × ℕ => g p.swap) 1 := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hv
  refine hsw.prod_fiberwise (fun i => ?_)
  have hsi : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹) := hsw.summable.prod_factor i
  have hsi' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (i + 2))⁻¹) := by
    rw [← summable_nat_add_iff 1]
    have e : (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ (i + 2))⁻¹) =
        fun n : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹ := by
      ext n; push_cast; congr 2; ring
    rw [e]; exact hsi
  have := (hasSum_nat_add_iff' 1).mpr hsi'.hasSum
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, one_pow, inv_one] at this
  have e : (fun n : ℕ => g (Prod.swap (i, n))) = fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ (i + 2))⁻¹ := by
    ext n; simp only [g, Prod.swap]; push_cast; congr 2; ring
  rw [e]; exact this
end Formalism.HermitianLatticeCounting.P
