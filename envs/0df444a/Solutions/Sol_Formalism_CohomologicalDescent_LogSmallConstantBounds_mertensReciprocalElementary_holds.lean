-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.mertensReciprocalElementary_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:54.709803+00:00
-- url     : https://prove2.me/submissions/316d973b-489e-4fe7-80db-166e49e25fb7

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_pr_eq_primesUpTo_floor
import Theorems.Thm_Formalism_CohomologicalDescent_sums_harmonic_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : MertensReciprocalElementary := by
  intro y hy
  rw [pr_eq_primesUpTo_floor]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊y⌋₊ := ⟨_, rfl⟩
  rw [← hn]
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.le_floor (by rw [Nat.cast_one]; exact hy)
  have hsub : Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n ⊆ (Finset.Icc 1 n).erase 1 := by
    intro p hp
    simp only [Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_erase, Finset.mem_Icc]
    exact ⟨hp.2.one_lt.ne', hp.2.one_lt.le, by omega⟩
  have s1 : ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (1 : ℝ) / (p : ℝ) ≤
      ∑ i ∈ (Finset.Icc 1 n).erase 1, (1 : ℝ) / (i : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have s2 := Finset.add_sum_erase (Finset.Icc 1 n) (fun i : ℕ => (1 : ℝ) / (i : ℝ))
    (Finset.mem_Icc.2 ⟨le_rfl, hn1⟩)
  simp only [Nat.cast_one, div_one] at s2
  have s3 := Formalism.CohomologicalDescent.sums_harmonic_real n
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have s4 : Real.log (n : ℝ) ≤ Real.log y := Real.log_le_log (by linarith)
    (by rw [hn]; exact Nat.floor_le (by linarith))
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
