-- Prove2me | solution 1 for Formalism.GM.ProgressionMeanBounds.binMatK_entry_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:23.28736+00:00
-- url     : https://prove2.me/submissions/5e2ee2ac-ef2a-4604-aa30-bdeca6725d7f

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Theorems.Thm_Formalism_GM_ProgressionMeanBounds_binK_natDegree_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Formalism.GM.ProgressionMeanBounds
open Finset Polynomial
namespace Formalism.GM.ProgressionMeanBounds
theorem _root_.solution (K : Type) [Field K] {n : ℕ} (del₀ : ℕ)
    (c : Fin n → Fin n → ℕ → K) (i j : Fin n) : ((binMatK K del₀ c) i j).natDegree ≤ del₀ := by
  unfold binMatK
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ del₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (natDegree_C_mul_le _ _).trans ((binK_natDegree_le K k).trans hk')
end Formalism.GM.ProgressionMeanBounds
