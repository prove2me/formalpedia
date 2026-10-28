-- Prove2me | solution 1 for CorruptRobustRL.ElimLB.union_bound_display
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:36:48.895723+00:00
-- url     : https://prove2.me/submissions/42a8bf43-8232-47df-82e9-040d9ffaac7d

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

open CorruptRobustRL.ElimLB


theorem solution (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (L : Learner (Fin (H + 1)) (Fin A) H) (K : ℕ) :
    ((runLaw (comboLock0 H A) L K).toOuterMeasure {run | ∀ k < K, admEv k run}).toReal -
        ∑ k ∈ Finset.range K,
          ((runLaw (comboLock0 H A) L K).toOuterMeasure
            ({run | combi k run} ∩ {run | admEv k run})).toReal ≤
      ((runLaw (comboLock0 H A) L K).toOuterMeasure
        ({run | ∀ k < K, ¬ combi k run} ∩ {run | ∀ k < K, admEv k run})).toReal := by
  set μ := (runLaw (comboLock0 H A) L K).toOuterMeasure with hμ
  have hfin : ∀ s, μ s ≠ ⊤ := by
    intro s
    have h1 : μ Set.univ = 1 := PMF.toOuterMeasure_apply_eq_one_iff _ _ |>.mpr (Set.subset_univ _)
    exact ((MeasureTheory.measure_mono (Set.subset_univ s)).trans_eq h1).trans_lt ENNReal.one_lt_top |>.ne
  have hsub : {run | ∀ k < K, admEv (H := H) (A := A) k run} ⊆
      ({run | ∀ k < K, ¬ combi (H := H) (A := A) k run} ∩ {run | ∀ k < K, admEv (H := H) (A := A) k run}) ∪
        ⋃ k ∈ Finset.range K, ({run | combi (H := H) (A := A) k run} ∩ {run | admEv (H := H) (A := A) k run}) := by
    intro run hrun
    by_cases hc : ∀ k < K, ¬ combi (H := H) (A := A) k run
    · exact Or.inl ⟨hc, hrun⟩
    · push_neg at hc
      obtain ⟨k, hk, hck⟩ := hc
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_range]
      exact ⟨k, hk, hck, hrun k hk⟩
  have h1 := (MeasureTheory.measure_mono (μ := μ) hsub).trans (MeasureTheory.measure_union_le _ _)
  have h2 := MeasureTheory.measure_biUnion_finset_le (μ := μ) (Finset.range K)
    (fun k => {run | combi (H := H) (A := A) k run} ∩ {run | admEv (H := H) (A := A) k run})
  have h3 : μ {run | ∀ k < K, admEv (H := H) (A := A) k run} ≤
      μ ({run | ∀ k < K, ¬ combi (H := H) (A := A) k run} ∩ {run | ∀ k < K, admEv (H := H) (A := A) k run}) +
        ∑ k ∈ Finset.range K, μ ({run | combi (H := H) (A := A) k run} ∩ {run | admEv (H := H) (A := A) k run}) :=
    h1.trans (add_le_add_right h2 _)
  have h4 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _,
    ENNReal.sum_ne_top.mpr (fun k _ => hfin _)⟩) h3
  rw [ENNReal.toReal_add (hfin _) (ENNReal.sum_ne_top.mpr (fun k _ => hfin _)),
    ENNReal.toReal_sum (fun k _ => hfin _)] at h4
  linarith
