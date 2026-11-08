-- Prove2me | solution 1 for CongestionTaxes.display_14_line_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:07:10.340379+00:00
-- url     : https://prove2.me/submissions/693f12aa-5cf4-46ff-b0a8-6da45bb00132

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_IsFeasible
import Definitions.Def_CongestionTaxes_IsSolution

open CongestionTaxes in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E)
    (a : ι → Finset E) (ha : CongestionPoA.AsymSum.IsProfile G a) :
    IsFeasible G (fun i s => if s = a i then 1 else 0)
        (fun r => (CongestionPoA.AsymSum.load a r : ℝ)) ∧
      ∀ y v, IsSolution G y v →
        ∑ r, poissonValue (G.latency r) (v r) ≤
          ∑ r, poissonValue (G.latency r) (CongestionPoA.AsymSum.load a r : ℝ) := by
  have hfeas : IsFeasible G (fun i s => if s = a i then 1 else 0)
      (fun r => (CongestionPoA.AsymSum.load a r : ℝ)) := by
    refine ⟨fun i s => ?_, fun i s hs => ?_, fun i => ?_, fun r => ?_⟩
    · by_cases h : s = a i <;> simp [h]
    · have : s ≠ a i := by rintro rfl; exact hs (ha i)
      simp only [this, if_false]
    · simp only
      rw [Finset.sum_ite_eq' (G.strategies i) (a i) (fun _ => (1 : ℝ)), if_pos (ha i)]
    · simp only
      unfold CongestionPoA.AsymSum.load
      rw [Finset.natCast_card_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_ite_eq' _ (a i) (fun _ => (1 : ℝ))]
      by_cases hr : r ∈ a i <;> simp [hr, ha i]
  refine ⟨hfeas, fun y v hsol => ?_⟩
  have := hsol.2 _ _ hfeas
  unfold objective at this
  exact this
