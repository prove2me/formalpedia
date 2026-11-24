-- Prove2me | solution 1 for Formalism.QuantumDeterminants.holomorphic_harish_chandra_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:38.70113+00:00
-- url     : https://prove2.me/submissions/ab5c9f3f-d934-4431-8709-adc9cab38b91

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK

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
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution : HolHC := by
  intro n a b h
  unfold IsHCParam lamHol
  refine ⟨?_, ?_⟩
  · intro i j hij
    try simp only
    have hij' : (i : ℕ) < j := hij
    have hj : j ≠ 0 := by
      rintro rfl
      exact Fin.not_lt_zero i hij
    rw [if_neg hj]
    have hj1 : (i : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij'
    by_cases hi : i = 0
    · rw [if_pos hi]
      have h1 : ((n : ℤ) : ℝ) < (b : ℝ) - a := by exact_mod_cast h
      have h2 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (j : ℕ))
      push_cast at h1
      linarith
    · rw [if_neg hi]
      linarith
  · intro i
    by_cases hi : i = 0
    · exact ⟨b - n, by rw [if_pos hi]; push_cast; ring⟩
    · exact ⟨a + 1 - (i : ℕ), by rw [if_neg hi]; push_cast; ring⟩
end Formalism.QuantumDeterminants
