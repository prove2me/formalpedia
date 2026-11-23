-- Prove2me | solution 1 for Formalism.DivisionValues.W8.telescope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:13.64377+00:00
-- url     : https://prove2.me/submissions/74d27556-a0de-4eb4-86ed-d1dce33fbbd3

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
namespace W8
private lemma sum_castSucc_sub_succ_eq_sub_last {n : ℕ} (c : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (c i.castSucc - c i.succ) = c 0 - c (Fin.last n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h : ∑ i : Fin m, (c i.castSucc.castSucc - c i.succ.castSucc) =
        c (0 : Fin (m + 1)).castSucc - c (Fin.last m).castSucc := ih (fun j => c j.castSucc)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [h]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    ring
end W8
open W8
namespace W8
end W8
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {n : ℕ} {c : Fin (n + 1) → ℝ} {c' : Fin n → ℝ} {S : ℝ}
    (h : Formalism.LatticeIndexTer.Interlaced n c c' S) : ∑ i : Fin n, (c i.castSucc - c' i) ≤ S := by
  have hsum : ∑ i : Fin n, (c i.castSucc - c' i) ≤ ∑ i : Fin n, (c i.castSucc - c i.succ) :=
    Finset.sum_le_sum fun i _ => by linarith [(h.2 i).2]
  rw [sum_castSucc_sub_succ_eq_sub_last] at hsum
  linarith [(h.1 0).2, (h.1 (Fin.last n)).1]
end Formalism.DivisionValues.W8
