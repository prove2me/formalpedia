-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.kapL_le_kap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:17.022257+00:00
-- url     : https://prove2.me/submissions/bdcec42e-1c23-4000-8b6a-c71710341af7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_logb_add_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {L : Type} [Fintype L] (d : L → ℕ) :
    kapL p r d + (Fintype.card L : ℝ) * r ≤ kap p r d := by
  unfold kapL kap lg
  have e : (Fintype.card L : ℝ) * r = ∑ _i : L, (r : ℝ) := by simp
  rw [e, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hl := logb_add_nonneg hp r (d i) (by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  split_ifs with h0
  · nlinarith
  · apply le_of_eq
    ring
end Formalism.MainNotions.PlaneGram
