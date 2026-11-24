-- Prove2me | solution 1 for Formalism.LatticeIndexTer.sumInterlacedBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:58.663609+00:00
-- url     : https://prove2.me/submissions/19670b0f-3380-42f4-80d9-6618c709aa95

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Theorems.Thm_Formalism_LatticeIndexTer_ph_mono
import Theorems.Thm_Formalism_LatticeIndexTer_one_le_log
import Theorems.Thm_Formalism_LatticeIndexTer_alt_bound
import Theorems.Thm_Formalism_LatticeIndexTer_phm_mono
import Theorems.Thm_Formalism_LatticeIndexTer_phm_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset
namespace Formalism.LatticeIndexTer
theorem _root_.solution : Interlace := by
  intro k c c' S w hI hw
  obtain ⟨hc, hc'⟩ := hI
  have hS : 0 ≤ S := le_trans (hc 0).1 (hc 0).2
  have e1 : ∀ x : ℝ, 1 ≤ x → phm x = ph x := fun x hx => by unfold phm; rw [max_eq_left hx]
  have hb : phm (w + c (Fin.last k)) ≤ (∑ i, phm (w + c i)) - ∑ i, phm (w + c' i) ∧
      (∑ i, phm (w + c i)) - ∑ i, phm (w + c' i) ≤ phm (w + c 0) :=
    alt_bound phm phm_mono k (fun i => w + c i) (fun i => w + c' i)
      (fun i => ⟨by show w + c' i ≤ w + c i.castSucc; linarith [(hc' i).1],
        by show w + c i.succ ≤ w + c' i; linarith [(hc' i).2]⟩)
  have s1 : (∑ i, phm (w + c i)) = ∑ i, ph (w + c i) :=
    Finset.sum_congr rfl fun i _ => e1 _ (by linarith [(hc i).1])
  have s2 : (∑ i, phm (w + c' i)) = ∑ i, ph (w + c' i) :=
    Finset.sum_congr rfl fun i _ => e1 _ (by linarith [(hc' i).2, (hc i.succ).1])
  rw [s1, s2] at hb
  have e0 : phm (w + c 0) = ph (w + c 0) := e1 _ (by linarith [(hc 0).1])
  have up : ph (w + c 0) ≤ ph (w + S) := ph_mono (by linarith [(hc 0).1]) (by linarith [(hc 0).2])
  have lo : -1 ≤ phm (w + c (Fin.last k)) := phm_ge
  have hL : 1 ≤ Real.log (w + S + 2) := one_le_log (by linarith)
  have hphS : ph (w + S) ≤ (w + 2 * S) * Real.log (w + S + 2) := by
    have hl := Real.log_le_log (by linarith : 0 < w + S) (by linarith : w + S ≤ w + S + 2)
    unfold ph
    nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ w + S),
      mul_nonneg hS (by linarith : 0 ≤ Real.log (w + S + 2))]
  have hp : 1 ≤ (w + 2 * S) * Real.log (w + S + 2) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w + 2 * S - 1) (by linarith : 0 ≤ Real.log (w + S + 2) - 1)]
  rw [abs_le]
  constructor
  · linarith [hb.1]
  · linarith [hb.2]
end Formalism.LatticeIndexTer
