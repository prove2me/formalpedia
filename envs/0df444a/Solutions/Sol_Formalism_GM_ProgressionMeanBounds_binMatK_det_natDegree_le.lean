-- Prove2me | solution 1 for Formalism.GM.ProgressionMeanBounds.binMatK_det_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:07.642822+00:00
-- url     : https://prove2.me/submissions/771237d3-9aa8-4e1b-8835-a96c5c296b0c

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Theorems.Thm_Formalism_GM_ProgressionMeanBounds_binMatK_entry_natDegree_le

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
    (c : Fin n → Fin n → ℕ → K) : ((binMatK K del₀ c).det).natDegree ≤ del₀ * n := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  rw [Units.smul_def]
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, ((binMatK K del₀ c) (σ i) i).natDegree ≤ ∑ _i : Fin n, del₀ :=
        Finset.sum_le_sum (fun i _ => binMatK_entry_natDegree_le K del₀ c (σ i) i)
    _ = del₀ * n := by simp [mul_comm]
end Formalism.GM.ProgressionMeanBounds
